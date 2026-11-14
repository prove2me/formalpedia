-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinning_output_sensitivity
-- name    : StabilityDichotomies.Solvability.thinning_output_sensitivity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:57:57.640458+00:00
-- url     : https://prove2.me/theorems/05ce06eb-3798-4c3f-bf02-caad7807b585
-- title:
--   Average sensitivity of the exact thinning output law
-- statement:
--   Let Γ be a finite Horn or dual-Horn language. There is a constant C > 0 depending only on Γ and the case such that, for every 0 < ε ≤ 1, every semantic solver with the exact output distribution of Definition 4.2 has average sensitivity at most C/ε on every satisfiable input. The statement isolates the source theorem’s sensitivity bound; it does not assert a computational implementation or runtime.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, sensitivity proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinning_output_sensitivity (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Solver Γ, ThinningOutputLaw Γ b ε A →
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  sorry
