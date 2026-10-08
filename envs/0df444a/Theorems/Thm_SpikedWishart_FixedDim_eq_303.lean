-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_eq_303
-- name    : SpikedWishart.FixedDim.eq_303
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:01.995745+00:00
-- url     : https://prove2.me/theorems/74d3372f-f1fb-4226-9952-aa6589a0c8ef
-- title:
--   §5, (303), p. 1691 — C = Π_{j=0}^{k−1}(1+j)!(M−k+j)! / (Mπ₁)^{Mk}
-- statement:
--   Let $M \ge k \ge 1$ and $\pi_1 > 0$. The normalizing constant
--   $$C = \int_{(0,\infty)^k} V(y)^2\prod_{j=1}^k e^{-M\pi_1 y_j}\,y_j^{M-k}\,dy_1\cdots dy_k,\qquad V(y)^2 = \prod_{i<j}|y_i-y_j|^2,$$
--   equals
--   $$C = \frac{\prod_{j=0}^{k-1}(1+j)!\,(M-k+j)!}{(M\pi_1)^{Mk}} .$$
--
--   This is the Laguerre case of Selberg's integral. It supplies the constant whose asymptotics, together with (304), produce the limit $G_k$ in Proposition 1.1.
--
--   **Formalization Note** $C$ is the integral of the unordered weight over the whole orthant, so the product includes the factor $k!$ from the $k!$ orderings (e.g. $k = 1$: $C = (M-1)!/(M\pi_1)^M$; $k=2$: $C = 2\,(M-2)!\,(M-1)!/(M\pi_1)^{2M}$).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1691, §5, (303)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

namespace SpikedWishart.FixedDim

theorem eq_303 (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) :
    C M k π₁ = (∏ j ∈ Finset.range k,
        ((1 + j).factorial : ℝ) * ((M - k + j).factorial : ℝ)) / ((M : ℝ) * π₁) ^ (M * k) := by sorry

end SpikedWishart.FixedDim
