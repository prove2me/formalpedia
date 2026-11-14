-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinning_output_approximates
-- name    : StabilityDichotomies.Solvability.thinning_output_approximates
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:51:56.863232+00:00
-- url     : https://prove2.me/theorems/d45ffb87-07ca-4eb0-8c3e-402abc5956f8
-- title:
--   Approximation guarantee for the Horn and dual-Horn thinning output law
-- statement:
--   Let Γ be Horn or dual-Horn, let 0 < ε ≤ 1, and let A be any solver with the exact output law of the thinning algorithm in Definition 4.2. Then A satisfies at least a 1−ε fraction of constraint occurrences in expectation on every satisfiable instance. This is the approximation guarantee in Theorem 4.3. It assumes the output-law relation and does not by itself construct the solver or prove its sensitivity bound.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinning_output_approximates (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A) : Approximates A ε := by sorry
