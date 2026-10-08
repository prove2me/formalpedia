-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_eq_302
-- name    : SpikedWishart.FixedDim.eq_302
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:26.081017+00:00
-- url     : https://prove2.me/theorems/d80e94b4-76cb-483e-a377-5ea100134b0b
-- title:
--   §5, (301)–(302), p. 1691 — for Σ = π₁⁻¹I_k, P(λ₁ ≤ t) = (1/C)∫_{(0,t]^k} V(y)²Πe^{−Mπ₁y_j}y_j^{M−k}dy
-- statement:
--   Let $M \ge k \ge 1$ and $\pi_1 > 0$. Take $M$ independent complex Gaussian samples of $k$ variables with mean zero and covariance $\Sigma = \pi_1^{-1} I_k$, let $S = \frac1M\sum_m \vec y_m\vec y_m^{\,*}$ and let $\lambda_1$ be its largest eigenvalue. Then for every real $t$,
--   $$\mathbb P(\lambda_1\le t) = \frac1C\int_0^t\!\!\cdots\int_0^t V(y)^2\prod_{j=1}^k e^{-M\pi_1y_j}\,y_j^{M-k}\,dy_1\cdots dy_k,$$
--   where $V(y)^2=\prod_{i<j}|y_i-y_j|^2$ and $C$ is the integral of the same weight over $(0,\infty)^k$.
--
--   Equivalently, the eigenvalues of $S$ have the joint density (301), $p(\lambda) = \frac1C V(\lambda)^2\prod_j e^{-M\pi_1\lambda_j}\lambda_j^{M-k}$ on $(0,\infty)^k$. This exact formula is the starting point of the proof of Proposition 1.1.
--
--   **Formalization Note** For $t \le 0$ both sides are $0$. The covariance is $\pi_1^{-1}I_k$, i.e. the sample model with $U = I$ and all population eigenvalues $\ell_j = \pi_1^{-1}$; a Hermitian matrix with a single eigenvalue is scalar, so this is the paper's hypothesis (300). The hypothesis $k \le M$ is implicit on the page (the exponent $M-k$; for $M<k$, $S$ is singular).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1691, §5, (300)–(302)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

namespace SpikedWishart.FixedDim

open MeasureTheory Set

theorem eq_302 (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (t : ℝ) :
    (sampleLaw M k).real {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
      (C M k π₁)⁻¹ * ∫ y in Set.pi univ (fun _ : Fin k => Ioc 0 t), w M π₁ y := by sorry

end SpikedWishart.FixedDim
