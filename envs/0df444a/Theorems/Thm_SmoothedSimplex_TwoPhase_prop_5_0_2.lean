-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_prop_5_0_2
-- name    : SmoothedSimplex.TwoPhase.prop_5_0_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:27:52.320867+00:00
-- url     : https://prove2.me/theorems/4ea55a6e-71c5-4592-84a0-766507808c3d
-- title:
--   Proposition 5.0.2 (trivial shadow bounds)
-- statement:
--   For every input $A,y,z$, sampled collection $\mathcal I$, and coefficient choice $\alpha$, the two shadow counts are bounded by the numbers of possible bases:
--   $$S'_z(A,y,\mathcal I,\alpha)\le\binom nd,\qquad S_z^+(A,y,\mathcal I)\le\binom n{d+1}.$$
--   These finite bounds control exceptional events in the later expectation estimates. The extra two pivots of LP⁺ are accounted for separately in $C$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Proposition 5.0.2, printed p. 59, PDF p. 59

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Proposition 5.0.2 (trivial shadow bounds), printed p. 59, PDF p. 59. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem prop_5_0_2 {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (z : Point d) (draw : Fin (sampleCount n d) → DSet n d)
    (α : Fin n → ℝ)
    (hαsum : ∑ i ∈ bestSample a draw, α i = 1)
    (hαlo : ∀ i ∈ bestSample a draw, 1 / (d : ℝ)^2 ≤ α i) :
    firstPhaseShadow a (bestSample a draw) α
      (scaleK a (bestSample a draw)) (scaleM a y) z ≤ Nat.choose n d ∧
    secondPhaseSteps a y z draw ≤ Nat.choose n (d + 1) := by sorry

end SmoothedSimplex.TwoPhase
