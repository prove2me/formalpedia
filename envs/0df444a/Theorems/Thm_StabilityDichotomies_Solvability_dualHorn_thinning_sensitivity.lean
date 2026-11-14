-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_dualHorn_thinning_sensitivity
-- name    : StabilityDichotomies.Solvability.dualHorn_thinning_sensitivity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:36:48.120913+00:00
-- url     : https://prove2.me/theorems/5421c9af-8d68-4fb5-8e04-820067db8443
-- title:
--   Exact-law dual-Horn thinning sensitivity is at most maximum arity over ε
-- statement:
--   Let Γ be dual-Horn and 0 < ε ≤ 1. Any solver with the exact greatest-solution thinning law has average sensitivity at most maxArity(Γ)/ε on every satisfiable instance. This is the dual-Horn sensitivity part of the source theorem, in the semantic output-law model; runtime is not asserted.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.dualHorn_thinning_sensitivity (Γ : Language)
    (hDualHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ)
    (hLaw : ThinningOutputLaw Γ true ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    averageSensitivity A I ≤ (maxArity Γ : ℝ) * ε⁻¹ := by sorry
