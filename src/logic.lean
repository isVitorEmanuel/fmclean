
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros P notP,
  apply notP,
  exact P,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro notnotP,
  by_contradiction p,
  apply notnotP,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
   split, {
    exact doubleneg_elim P,
  }, {
    exact doubleneg_intro P,
  }
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro porq,
  cases porq with P Q, {
    right,
    exact P,
  }, {
    left,
    exact Q,
  }
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pandq,
  cases pandq with h_p h_q,
  split, {
    exact h_q,
  }, {
    exact h_p,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros nPorQ P,
  cases nPorQ with nP Q, {
    contradiction,
  }, {
    exact Q,
  }
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros PorQ notP,
  cases PorQ with P Q, {
    exfalso,
    apply notP, 
    exact P,
  }, {
    exact Q,
  }
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros PinQ notQ P,
  have hQ : Q := PinQ P,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros notQinnotP p,
  by_cases nQ : Q,{
    exact nQ,
  }, {
    by_contradiction,
    have nP : ¬P := notQinnotP(nQ),
    apply nP(p),
  }
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,{
    apply impl_as_contrapositive P Q,
  }, {
    apply impl_as_contrapositive_converse P Q,
  }
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro npp,
  apply npp,
  right,
  intro p,
  apply npp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp nnp,
  apply nnp,
  apply pqp,
  intro p,
  exfalso,
  have n : false := nnp(p),
  exact n,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros porq npnq,
  cases porq with p q,{
    cases npnq with np nq,
      contradiction,
  }, {
    cases npnq with np nq,
      contradiction,
  }
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros pq npnq,
  cases npnq with np nq,{
    cases pq with p q,
      contradiction,
  }, {
    cases pq with p q,
      contradiction,
  }
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,{
    intro p,
    apply npq,
    left,
    exact p,
  }, {
    intro q,
    apply npq,
    right,
    exact q,
  }
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npnq pq,
  cases npnq with np nq,
    cases pq with p q,{
      contradiction,
    }, {
      contradiction,
    }
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases h : P,{
    left,
    intro q,
    apply npq,
    split,{
      exact h,
    }, {
      exact q,
    }
  }, {
    right,
    exact h,
  }
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nqnp pq,
  cases nqnp with nq np,{
    cases pq with p q,
      contradiction,
  }, {
    cases pq with p q,
      contradiction,
  }
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,{
    apply demorgan_conj,
  }, {
    apply demorgan_conj_converse,
  }
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split, {
    apply demorgan_disj,
  }, {
    apply demorgan_disj_converse,
  }
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  cases qr with q r, {
    left,
    split, {
      exact p,
    }, {
      exact q,
    }
  }, {
    right,
    split, {
      exact p,
    }, {
      exact r,
    }
  }
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr, {
    split, {
      cases pq with p q,
      exact p,
    }, {
      cases pq with p q,
      left,
      exact q,
    }
  }, {
    split, {
      cases pr with p r,
      exact p,
    }, {
      cases pr with p r,
      right,
      exact r,
    }
  }
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split, {
    cases pqr with p qr, {
      left,
      exact p,
    }, {
      cases qr with q r,
      right,
      exact q,
    }
  }, {
    cases pqr with p qr, {
      left,
      exact p,
    }, {
      cases qr with q r,
      right,
      exact r,
    }
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq with p q,{
    left,
    exact p,
  }, {
    cases pr with p r, {
      left,
      exact p,
    }, {
      right,
      split, {
        exact q,
      }, {
        exact r,
      }
    }
  }
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros pqr p q,
  apply pqr,
  split, {
    exact p,
  }, {
    exact q,
  },
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros pqr pq,
  cases pq with p q,
  have qr : Q→R := pqr(p),
  have r : R := qr(q),
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split, {
    intro pp,
    cases pp with p p,
    exact p,
  }, {
    intro p,
    split, {
      exact p,
    }, {
      exact p,
    }
  }
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split, {
    intro pp,
    cases pp with p p, {
      exact p,
    }, {
      exact p,
    }
  }, {
    intro p,
    right,
    exact p,
  }
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros nEx x Px,
  apply nEx,
  existsi x,
  exact Px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros Au Eu,
  cases Eu with u Pu,
  apply Au(u),
  exact Pu,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro nAu,
  by_contradiction nEu,
  apply nAu,
  intro u,
  by_contradiction nPu,
  apply nEu,
  existsi u,
  exact nPu,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros Enu nAu,
  cases Enu with u nPu,
  have Pu : P u := nAu(u),
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split, {
    apply demorgan_forall,
  }, {
    apply demorgan_forall_converse,
  }
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split, {
    intros nEu u Pu,
    apply nEu,
    existsi u,
    exact Pu,
  }, {
    apply demorgan_exists_converse,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
