-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_algorithm_upper
-- name    : StabilityDichotomies.Bijunctive.bijunctive_algorithm_upper
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T07:47:25.137123+00:00
-- url     : https://prove2.me/theorems/4e615a03-0bb7-4029-bd72-edd9ebb3695b
-- title:
--   Exact-law approximation and sensitivity upper bound for the bijunctive algorithm
-- statement:
--   Let Γ be a finite majority-closed Boolean language and fix a correct bounded two-CNF representation. There is C > 0, depending on the fixed language and representation, such that for every 0 < ε ≤ 1 a semantic solver with the exact product-measure output law of Definition 4.8 is a (1−ε)-approximation and has average sensitivity at most C ε⁻¹ log |V| on every satisfiable instance with at least two variables. The formalization represents the source output distribution and rates, but not executable runtime; normalization, measurability, and the approximation and sensitivity proofs are open obligations.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, §4.2.2, Definition 4.8 and Theorem 4.9, pp. 19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_algorithm_upper (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, BijunctiveOutputLaw Γ rep ε A ∧ Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  sorry
