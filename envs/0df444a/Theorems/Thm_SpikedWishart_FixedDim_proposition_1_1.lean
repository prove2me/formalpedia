-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_proposition_1_1
-- name    : SpikedWishart.FixedDim.proposition_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:20.509077+00:00
-- url     : https://prove2.me/theorems/0aeeb324-66f7-4c8b-813d-8c75c8351f58
-- title:
--   Proposition 1.1, p. 1652 — with N = k fixed and ℓ₁ = ⋯ = ℓ_k, √M(λ₁ − ℓ₁)/ℓ₁ ⇒ G_k and λ₁ → ℓ₁ in probability
-- statement:
--   Fix an integer $k\ge1$ and $\ell_1>0$. For each $M$, take $M$ independent complex Gaussian samples $\vec y_1,\dots,\vec y_M$ of $N = k$ variables with mean zero and covariance $\Sigma = \ell_1 I_k$ (all population eigenvalues equal, $\ell_1=\cdots=\ell_k$), form the sample covariance matrix $S = \frac1M\sum_{m=1}^M\vec y_m\vec y_m^{\,*}$ and let $\lambda_1$ be its largest eigenvalue. Then, as $M\to\infty$ with $k$ fixed:
--
--   1. for every real $x$,
--   $$\lim_{M\to\infty}\mathbb P\Big((\lambda_1-\ell_1)\,\frac1{\ell_1}\sqrt M\le x\Big) = G_k(x);$$
--   2. $\lambda_1\to\ell_1$ in probability: for every $\varepsilon>0$, $\mathbb P(|\lambda_1-\ell_1|>\varepsilon)\to0$.
--
--   Here $G_k$ is the distribution function of the largest eigenvalue of the $k\times k$ Gaussian unitary ensemble, Definition 1.2. The proposition contrasts with Theorem 1.1(b) of the paper: when the dimension stays fixed, the largest eigenvalue fluctuates on the scale $M^{-1/2}$ with the same GUE limit, without the additional bias term that appears when $N\to\infty$.
--
--   **Formalization Note** The page prints (50) as "$\mathbb P\big((\lambda_1-\ell_1)\frac1{\ell_1}\sqrt Mx\big)$" with the "$\le$" missing; the intended event $(\lambda_1-\ell_1)\frac1{\ell_1}\sqrt M\le x$ is stated. A Hermitian matrix all of whose eigenvalues equal $\ell_1$ is $\ell_1 I_k$, so the sample model is taken with $U = I$ and $\ell_j = \ell_1$; this is the page's hypothesis (49), not a special case. Samples are mean-zero and uncentred, with $E|g|^2 = 1$ per complex coordinate, as in the paper's formula (59).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1652, Proposition 1.1, (49)–(51); proof p. 1691, §5

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE

namespace SpikedWishart.FixedDim

open MeasureTheory Filter Topology

theorem proposition_1_1 (k : ℕ) (hk : 1 ≤ k) (ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁) :
    (∀ x : ℝ, Tendsto (fun M : ℕ => (sampleLaw M k).real
        {Y | (SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁) * (1 / ℓ₁) * Real.sqrt M ≤ x})
        atTop (𝓝 (G k x))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun M : ℕ => (sampleLaw M k).real
        {Y | ε < |SpikedWishart.Separated.largestEig M 1 (fun _ => ℓ₁) Y - ℓ₁|}) atTop (𝓝 0)) := by sorry

end SpikedWishart.FixedDim
