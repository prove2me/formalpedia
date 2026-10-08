-- Prove2me | Theorems.Thm_SpikedWishart_Separated_eq_287_295
-- name    : SpikedWishart.Separated.eq_287_295
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:17.572092+00:00
-- url     : https://prove2.me/theorems/fbb49035-67a5-49d2-9423-1ab9bb422841
-- title:
--   (287) and (295), pp. 1689–1690 — p_k′ = √k p_{k−1} and p_k″ − y p_k′ + k p_k = 0
-- statement:
--   Let $p_n$ be the orthonormal polynomials for the weight $e^{-x^2/2}$ on $\mathbb R$ (31). Then for every $k \ge 1$ and $y \in \mathbb R$,
--   $$
--   p_k'(y) = \sqrt k\, p_{k-1}(y), \tag{287}
--   $$
--   and for every $k \ge 0$ and $y \in \mathbb R$,
--   $$
--   p_k''(y) - y\,p_k'(y) + k\,p_k(y) = 0. \tag{295}
--   $$
--
--   These are the forward-shift formula and the Hermite differential equation in the normalisation of $p_k$; they turn the limiting kernel into the Christoffel–Darboux form.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1689, (287); p. 1690, (295)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_GUE

namespace SpikedWishart.Separated

/-- (287) and (295), pp. 1689–1690: `p_k' = √k p_{k−1}` (`k ≥ 1`) and
`p_k'' − y p_k' + k p_k = 0` (`k ≥ 0`). -/
theorem eq_287_295 :
    (∀ (k : ℕ), 1 ≤ k → ∀ y : ℝ, deriv (p k) y = Real.sqrt k * p (k - 1) y) ∧
    (∀ (k : ℕ) (y : ℝ), deriv (deriv (p k)) y - y * deriv (p k) y + k * p k y = 0) := by sorry

end SpikedWishart.Separated
