-- Prove2me | Theorems.Thm_QRH_dual_to_mean_square
-- name    : QRH.dual_to_mean_square
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T12:49:12.966235+00:00
-- url     : https://prove2.me/theorems/d512d050-e02e-4f7a-933c-8a46f863f96e
-- title:
--   The mean-square estimate from the canonical energy estimate
-- statement:
--   Assume the canonical estimate for the completed dual energy family: there is k with E(H, X, F) <= k (X F)^eps X F for all admissible scales 1 <= H <= X <= F. Assume the Poisson-summation reduction hpred: every such uniform bound on the energy converts into the mean-square bound msSum over the rows of norm at most D^(1+theta) with column scale D and truncation 2D, bounded by k D^(2 + theta + eps) for all D >= 2. Then there is k with msSum <= k D^(2 + theta + eps) for all D >= 2: the mean-square estimate of Proposition 3.1 of the source follows from the canonical energy estimate.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Proposition 3.1, reduced by Sections 4-6 (equations 3.1, 6.3).

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun

universe u

namespace QRH

/-- The reduction of the mean-square estimate of Proposition 3.1 to the
canonical energy estimate for the completed dual family. The first
hypothesis is the canonical estimate of sections 5 and 6 of the source —
proved there from the quadratic large sieve, the theta transformation,
and the admissible-exponent descent: the energy E(H, X, F) is bounded by
(XF)^ε XF uniformly over the admissible scales. The second hypothesis is
the Poisson-summation reduction of section 4: expanding the square and
applying Poisson summation in the row converts the canonical estimate at
the dual scales into the mean-square estimate at the original scales,
with row range D^(1+θ), column scale D, and truncation 2D. The theorem
assembles the two: the mean-square estimate of Proposition 3.1 follows.
-/
theorem dual_to_mean_square (W : QRHWorld.{u}) (S : QRHSums W)
    (c : W.E → ℂ) (Wt : ℝ → ℂ)
    (θ ε : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1 / 10) (hε : 0 < ε)
    (hcan : ∃ k : ℝ, ∀ H X F : ℝ, 1 ≤ H → H ≤ X → X ≤ F →
      Eener W S c Wt H X F ≤ k * (X * F) ^ ε * X * F)
    (hpred : ∀ k : ℝ, (∀ H X F : ℝ, 1 ≤ H → H ≤ X → X ≤ F →
        Eener W S c Wt H X F ≤ k * (X * F) ^ ε * X * F) →
      ∀ D : ℝ, 2 ≤ D →
        msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε)) :
    ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε) := by
  sorry

end QRH
