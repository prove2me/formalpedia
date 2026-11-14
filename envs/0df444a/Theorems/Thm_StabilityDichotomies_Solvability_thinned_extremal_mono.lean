-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinned_extremal_mono
-- name    : StabilityDichotomies.Solvability.thinned_extremal_mono
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:41:49.429912+00:00
-- url     : https://prove2.me/theorems/85c48020-119d-43ae-aebe-157bb940f6f9
-- title:
--   Monotonicity of extremal solutions under constraint insertion
-- statement:
--   For a satisfiable instance over a Horn language, adding constraint occurrences can only increase the coordinatewise least solution. For a dual-Horn language, adding occurrences can only decrease the coordinatewise greatest solution. The instance retains its entire variable set, and the two subsets are represented by Boolean masks over the same occurrence list. This is the monotonicity step in the average-sensitivity argument of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinned_extremal_mono (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (small big : Fin I.constraints.card → Bool)
    (h : ∀ i, small i = true → big i = true) :
    if b then extremalSolution (thinnedInstance I big) b ≤ extremalSolution (thinnedInstance I small) b
    else extremalSolution (thinnedInstance I small) b ≤ extremalSolution (thinnedInstance I big) b := by sorry
