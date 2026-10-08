-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_constant_limit
-- name    : SpikedWishart.FixedDim.constant_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:59.7452+00:00
-- url     : https://prove2.me/theorems/b39d5805-8563-407e-a191-fda663ea38cb
-- title:
--   §5, p. 1691 — as M → ∞ with k fixed, π₁^{kM}M^{k²/2}e^{kM}C → (2π)^{k/2}Π_{j=0}^{k−1}(1+j)!
-- statement:
--   Fix an integer $k\ge1$ and $\pi_1>0$, and let $C = C(M)$ be the normalizing constant of (302),
--   $$C(M) = \int_{(0,\infty)^k} V(y)^2\prod_{j=1}^k e^{-M\pi_1 y_j}\,y_j^{M-k}\,dy .$$
--   Then
--   $$\lim_{M\to\infty}\pi_1^{kM}M^{k^2/2}e^{kM}\,C(M) = (2\pi)^{k/2}\prod_{j=0}^{k-1}(1+j)! .$$
--
--   This is the asymptotics of the prefactor in (304). Since $\prod_{j=0}^{k-1}(1+j)! = \prod_{j=1}^k j!$, the limit equals $Z_k$ of (27), which is what makes the limit in Proposition 1.1 a probability distribution.
--
--   **Formalization Note** $C(M)$ is the integral of the definitions file; for $M < k$ the natural-number exponent $M-k$ is truncated to $0$, which affects only finitely many terms of the sequence.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1691, §5, sentence after (304)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

namespace SpikedWishart.FixedDim

open Filter Topology

theorem constant_limit (k : ℕ) (hk : 1 ≤ k) (π₁ : ℝ) (hπ₁ : 0 < π₁) :
    Tendsto (fun M : ℕ => π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * Real.exp ((k : ℝ) * M) *
        C M k π₁) atTop
      (𝓝 ((2 * Real.pi) ^ ((k : ℝ) / 2) * ∏ j ∈ Finset.range k, ((1 + j).factorial : ℝ))) := by sorry

end SpikedWishart.FixedDim
