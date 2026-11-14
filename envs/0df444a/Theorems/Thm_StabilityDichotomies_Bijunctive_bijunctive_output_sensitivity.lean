-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_sensitivity
-- name    : StabilityDichotomies.Bijunctive.bijunctive_output_sensitivity
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T08:07:44.067635+00:00
-- url     : https://prove2.me/theorems/e2e5792e-a636-4f43-ae95-05e0ae2f698e
-- title:
--   Average sensitivity of the exact bijunctive output law
-- statement:
--   Fix correct bounded two-CNF representations. There is C > 0 such that, for every 0 < ε ≤ 1, every solver with the exact Definition 4.8 product-measure output law has average sensitivity at most C ε⁻¹ log |V| on every satisfiable instance with at least two variables. This is the sensitivity half of Theorem 4.9; its coupling, path and root-change bounds remain open.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, pp. 19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_output_sensitivity (Γ : Language) (rep : TwoCNFRepresentation Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Solver Γ, BijunctiveOutputLaw Γ rep ε A →
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  sorry
