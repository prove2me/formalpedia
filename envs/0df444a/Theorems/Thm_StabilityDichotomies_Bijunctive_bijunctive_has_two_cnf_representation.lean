-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_has_two_cnf_representation
-- name    : StabilityDichotomies.Bijunctive.bijunctive_has_two_cnf_representation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:47:30.288752+00:00
-- url     : https://prove2.me/theorems/14d05b2d-74b3-4768-abc3-078f1cb3437b
-- title:
--   A majority-closed Boolean language has fixed two-CNF representations
-- statement:
--   Every finite Boolean constraint language closed under coordinatewise majority has a fixed correct two-CNF representation for each relation and a positive common finite clause bound. This formalizes the representation assumed at the start of the source paper’s bijunctive algorithm.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, §4.2.2, Definition 4.8 and Theorem 4.9, pp. 19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_has_two_cnf_representation (Γ : Language)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    Nonempty (TwoCNFRepresentation Γ) := by
  sorry
