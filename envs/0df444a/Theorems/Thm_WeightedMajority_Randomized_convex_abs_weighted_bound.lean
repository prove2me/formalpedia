-- Prove2me | Theorems.Thm_WeightedMajority_Randomized_convex_abs_weighted_bound
-- name    : WeightedMajority.Randomized.convex_abs_weighted_bound
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-07T20:08:51.549016+00:00
-- url     : https://prove2.me/theorems/371d2617-ff4d-4691-818a-8add88fafcb6
-- title:
--   Convex-combination triangle-inequality bound (Weighted Majority child A)
-- statement:
--   For nonneg weights w_i with positive total s = sum w_i, and values x_i
--   in [0,1], the absolute deviation of the weighted mean from any rho, scaled
--   by the total weight, is bounded by the weighted absolute deviations:
--
--   |sum_i w_i x_i / s - rho| * s <= sum_i w_i * |x_i - rho|.
--
--   Proof: multiply through by s > 0, so LHS = |sum_i w_i*(x_i - rho)|, then
--   triangle inequality with w_i >= 0. This is the convex-combination step in
--   the Weighted Majority regret-bound proof (Littlestone-Warmuth 1994,
--   Theorem 6.1, p. 240): s^(j+1) <= s^(j)*(1-(1-beta)|gamma^(j)-rho^(j)|)
--   needs sum w|x-rho| >= s|gamma-rho|. Pure real analysis, no probability.
-- source:
--   Littlestone-Warmuth, 'The Weighted Majority Algorithm', Information and Computation 108 (1994), Theorem 6.1, p. 240: the per-trial convex-combination step in the deterministic potential-drop argument (sum_i w_i|x_i-rho| >= s|gamma-rho|). Child A of the theorem_6_1 decomposition.

import Mathlib
set_option autoImplicit false

namespace WeightedMajority.Randomized

/-- Convex-combination triangle-inequality bound (child A of the
`theorem_6_1` decomposition, Littlestone-Warmuth 1994, p. 240): for
nonneg weights with positive total, multiplying the absolute deviation
of the weighted mean through by the total weight gives
`|sum w*x - rho * sum w| = |sum w*(x-rho)| <= sum w*|x-rho|`. -/
theorem convex_abs_weighted_bound {n : Nat} (w x : Fin n -> Real) (rho : Real)
    (hw : forall i, 0 <= w i) (hx : forall i, 0 <= x i /\ x i <= 1)
    (hpos : 0 < Finset.sum Finset.univ (fun i => w i)) :
    abs (Finset.sum Finset.univ (fun i => w i * x i)
      / Finset.sum Finset.univ (fun i => w i) - rho)
      * Finset.sum Finset.univ (fun i => w i)
      <= Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) := by sorry

end WeightedMajority.Randomized
