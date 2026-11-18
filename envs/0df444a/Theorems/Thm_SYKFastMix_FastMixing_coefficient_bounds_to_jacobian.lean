-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_coefficient_bounds_to_jacobian
-- name    : SYKFastMix.FastMixing.coefficient_bounds_to_jacobian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:51:46.45225+00:00
-- url     : https://prove2.me/theorems/3a0ab7cb-b414-4abb-b2ba-85612aa1817c
-- title:
--   From coefficient bounds to uniform Jacobian estimates
-- statement:
--   Let $Q$ be an SYK model with coupling scale $J>0$, and fix a disorder realization $w$. Let $F_m$ and $M_m$ denote the fermionic Jacobian and block-operator Taylor coefficients of equation (5.7). Suppose that for every integer $m\ge 1$,
--
--   $$\|F_m\|\le (133J)^m,$$
--
--   and for every integer $m\ge0$,
--
--   $$\|M_m\|\le (m+1)(133J)^{m+1}.$$
--
--   Then at every real $s$ satisfying $133J|s|<1$, both Taylor series converge to their specified operators and
--
--   $$\|\mathcal F(s)-I\|\le\frac{133J|s|}{1-133J|s|},\qquad\|\mathcal M(s)\|\le\frac{133J}{(1-133J|s|)^2}.$$
--
--   This deterministic implication separates the analytic summation step from the probabilistic control of the coefficients.
-- source:
--   Cai, Zhan, Zlokapa, Fast mixing of the SYK model at high temperatures, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1050.pdf, p.24 Eq. (5.7) and p.28 Eqs. (5.35)-(5.36), coefficient bounds Eq. (5.32).

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
noncomputable section
open scoped Matrix.Norms.L2Operator
open SYKFastMix.FastMixing

theorem SYKFastMix.FastMixing.coefficient_bounds_to_jacobian {N : ℕ} (Q : Model N) (w : Disorder N)
    (hF : ∀ m : ℕ, 1 ≤ m → SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m)
    (hM : ∀ m : ℕ, SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1) * (133 * Q.J)^(m+1)) :
    ∀ s : ℝ, 133 * Q.J * |s| < 1 →
      SYKEdge.opNorm (jacobian Q w s - 1) ≤ 133 * Q.J * |s| / (1 - 133 * Q.J * |s|) ∧
      SYKEdge.opNorm (blockM Q w s) ≤ 133 * Q.J / (1 - 133 * Q.J * |s|)^2 ∧
      HasSum (fun m : ℕ => (s : ℂ)^m • fermionCoefficient Q w m) (jacobian Q w s) ∧
      HasSum (fun m : ℕ => (s : ℂ)^m • mCoefficient Q w m) (blockM Q w s) := by sorry
