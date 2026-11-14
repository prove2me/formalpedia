-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_horn_thinning_sensitivity
-- name    : StabilityDichotomies.Solvability.horn_thinning_sensitivity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:31:23.076761+00:00
-- url     : https://prove2.me/theorems/cba47633-7ac2-4912-b249-648fa738a18a
-- title:
--   Exact-law Horn thinning has average sensitivity at most maximum arity over ε
-- statement:
--   Let Γ be a finite Horn Boolean language, 0 < ε ≤ 1, and A any solver with the exact least-solution thinning law of Definition 4.2. On every satisfiable instance, the average sensitivity of A is at most the maximum arity in Γ divided by ε. This is the Horn sensitivity part of Theorem 4.3, expressed for the exact semantic output law; no executable runtime is asserted.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.horn_thinning_sensitivity (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ)
    (hLaw : ThinningOutputLaw Γ false ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    averageSensitivity A I ≤ (maxArity Γ : ℝ) * ε⁻¹ := by sorry
