-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_eq_304
-- name    : SpikedWishart.FixedDim.eq_304
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:02.324745+00:00
-- url     : https://prove2.me/theorems/c030c012-bac1-400b-b20d-9b3b8b50ab1c
-- title:
--   §5, (304), p. 1691 — P(λ₁ ≤ 1/π₁ + x/(π₁√M)) = e^{−kM}/(π₁^{kM}M^{k²/2}C) ∫_{[−√M,x]^k} V(ξ)²Πe^{−√Mξ_j}(1+ξ_j/√M)^{M−k}dξ
-- statement:
--   Let $M \ge k \ge 1$, $\pi_1>0$, and let $\lambda_1$ be the largest eigenvalue of the sample covariance matrix of $M$ complex Gaussian samples of $k$ variables with covariance $\pi_1^{-1}I_k$. Let $C$ be the normalizing constant of (302). Then for every real $x \ge -\sqrt M$,
--   $$\mathbb P\Big(\lambda_1\le \frac1{\pi_1}+\frac{x}{\pi_1\sqrt M}\Big) = \frac{e^{-kM}}{\pi_1^{kM}M^{k^2/2}C}\int_{-\sqrt M}^x\!\!\cdots\int_{-\sqrt M}^x V(\xi)^2\prod_{j=1}^k e^{-\sqrt M\xi_j}\Big(1+\frac{\xi_j}{\sqrt M}\Big)^{M-k}d\xi_1\cdots d\xi_k .$$
--
--   The identity is (302) after the change of variables $y_j = \frac1{\pi_1}\big(1+\frac{\xi_j}{\sqrt M}\big)$. It puts the distribution of the rescaled largest eigenvalue into a form whose integrand converges pointwise to $V(\xi)^2\prod_j e^{-\xi_j^2/2}$ as $M\to\infty$.
--
--   **Formalization Note** The restriction $x \ge -\sqrt M$ is implicit on the page (the integration limits); at $x = -\sqrt M$ both sides are $0$. As in (302), the covariance is $\pi_1^{-1}I_k$ and $k \le M$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1691, §5, (304)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

namespace SpikedWishart.FixedDim

open MeasureTheory Set

theorem eq_304 (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (x : ℝ)
    (hx : -Real.sqrt M ≤ x) :
    (sampleLaw M k).real
        {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ 1 / π₁ + x / (π₁ * Real.sqrt M)} =
      Real.exp (-((k : ℝ) * M)) / (π₁ ^ (k * M) * (M : ℝ) ^ ((k : ℝ) ^ 2 / 2) * C M k π₁) *
        ∫ ξ in Set.pi univ (fun _ : Fin k => Icc (-Real.sqrt M) x),
          vandSq ξ * ∏ j, Real.exp (-Real.sqrt M * ξ j) * (1 + ξ j / Real.sqrt M) ^ (M - k) := by sorry

end SpikedWishart.FixedDim
