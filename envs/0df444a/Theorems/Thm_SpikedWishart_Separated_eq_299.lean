-- Prove2me | Theorems.Thm_SpikedWishart_Separated_eq_299
-- name    : SpikedWishart.Separated.eq_299
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:47.989254+00:00
-- url     : https://prove2.me/theorems/a8e13021-0a65-4d59-a269-8d2e3298da5b
-- title:
--   (299), p. 1690 — K₂(u,v) = √k e^{−εu}(p_k(u)p_{k−1}(v) − p_{k−1}(u)p_k(v))/(u−v) · e^{−v²/2}e^{εv}
-- statement:
--   Let $k \ge 1$, $\varepsilon > 0$, and $K_2(u,v) = \int_0^\infty\mathcal H_\infty(u+y)\mathcal J_\infty(v+y)\,dy$ (293). Then for all real $u \ne v$,
--   $$
--   K_2(u,v) = \sqrt k\,e^{-\varepsilon u}\,\frac{p_k(u)p_{k-1}(v) - p_{k-1}(u)p_k(v)}{u-v}\,e^{-v^2/2}e^{\varepsilon v}.
--   $$
--
--   Up to conjugation by $e^{\pm\varepsilon u}$ and $e^{\pm u^2/4}$, this is the kernel $H^{(k)}$ of (34), so the limiting Fredholm determinant is $\det(1 - H^{(k)}_x)$.
--
--   **Formalization Note** The identity is stated off the diagonal; on $u = v$ the right side is understood as its continuous extension, which is not part of the statement.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1690, (293) and (299)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_Separated_Kernels

namespace SpikedWishart.Separated

/-- (299), p. 1690: for `k ≥ 1`, `ε > 0` and `u ≠ v`,
`K₂(u, v) = √k e^{−εu} (p_k(u)p_{k−1}(v) − p_{k−1}(u)p_k(v))/(u − v) · e^{−v²/2} e^{εv}`. -/
theorem eq_299 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (u v : ℝ) (huv : u ≠ v) :
    K2 k ε u v =
      ((Real.sqrt k * Real.exp (-(ε * u)) *
          ((p k u * p (k - 1) v - p (k - 1) u * p k v) / (u - v)) *
          Real.exp (-(v ^ 2) / 2) * Real.exp (ε * v) : ℝ) : ℂ) := by sorry

end SpikedWishart.Separated
