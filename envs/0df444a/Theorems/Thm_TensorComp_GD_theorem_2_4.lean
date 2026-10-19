-- Prove2me | Theorems.Thm_TensorComp_GD_theorem_2_4
-- name    : TensorComp.GD.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:34.838351+00:00
-- url     : https://prove2.me/theorems/ab0b0237-aecb-4079-bffb-c2a98d94125d
-- title:
--   Theorem 2.4, p. 8 (ρ corrected to 1 − λ⋆_min^{4/3}η/5) — spectrally initialized vanilla GD: dist_F, dist_2,∞ ≤ (Cρᵗ + C′ noise)‖U⋆‖ for all t ≤ d⁵, w.p. ≥ 1 − δ
-- statement:
--   Let $T^\star=\sum_{i=1}^r u_i^{\star\otimes 3}\in\mathbb R^{d\times d\times d}$ be a symmetric rank-$r$ tensor with nonzero factors $U^\star=[u^\star_1,\dots,u^\star_r]$, and write $\lambda^\star_{\min}=\min_i\|u^\star_i\|_2^3$, $\lambda^\star_{\max}=\max_i\|u^\star_i\|_2^3$, $\kappa$ for the condition number and $\mu$ for the incoherence parameter of Definition 2.1. Each sorted index $j\le k\le l$ is observed independently with probability $p\in(0,1]$, with independent, mean-zero, sub-Gaussian noise of variance at most $\sigma^2$; the observation is $T=\mathcal P_\Omega(T^\star+E)$. Algorithm 2 (spectral subspace estimate) and Algorithm 3 ($L$ Gaussian restarts and pruning with threshold $\epsilon_{\mathsf{th}}$) produce $U^0$, and Algorithm 1 runs vanilla gradient descent $U^{t+1}=U^t-\eta\nabla f(U^t)$ with a constant step size.
--
--   Fix $\delta\in(0,1)$ and bounds on $r$, $\kappa$ and $\mu$ (the paper's "$r,\kappa,\mu=O(1)$"). Suppose
--   $$p\ge c_0\frac{\log^4 d}{d^{3/2}},\qquad \frac{\sigma}{\lambda^\star_{\min}}\le c_1\frac{\sqrt p}{d^{3/4}\log^2 d},\qquad L=c_2,\qquad \epsilon_{\mathsf{th}}=c_3\left(\frac{\log d}{d\sqrt p}+\frac{\sigma}{\lambda^\star_{\min}}\sqrt{\frac{d\log^2 d}{p}}+\sqrt{\frac{\log d}{d}}\right)$$
--   for suitable constants $c_0,c_2$ (large) and $c_1,c_3$ (small), $d$ is large enough, and $0<\eta\le\lambda^{\star\,4/3}_{\min}/(32\lambda^{\star\,8/3}_{\max})$. Then, with $\rho=1-\lambda^{\star\,4/3}_{\min}\eta/5$, with probability at least $1-\delta$ the algorithm runs to completion and every admissible execution satisfies, simultaneously for all $0\le t\le d^5$,
--   $$\operatorname{dist}_F(U^t,U^\star)\le\left(C_1\rho^t+C_2\frac\sigma{\lambda^\star_{\min}}\sqrt{\frac{d\log d}{p}}\right)\|U^\star\|_F,$$
--   $$\operatorname{dist}_\infty(U^t,U^\star)\le\operatorname{dist}_{2,\infty}(U^t,U^\star)\le\left(C_3\rho^t+C_4\frac\sigma{\lambda^\star_{\min}}\sqrt{\frac{d\log d}{p}}\right)\|U^\star\|_{2,\infty},$$
--   where $\operatorname{dist}$ minimizes over column permutations and $0<C_1,C_3<1$, $C_2,C_4>0$ are constants depending only on $\delta$ and the bound on $\kappa$.
--
--   This is the paper's headline guarantee: a spectral initialization followed by plain gradient descent, with no regularization or projection, converges linearly to an estimate whose Frobenius and row-wise errors are at the noise level.
--
--   **Formalization Note.** (1) The page calls $\rho<1$ an absolute constant for every admissible $\eta$; that is false as $\eta\to0$, so $\rho$ is pinned to $1-\lambda^{\star\,4/3}_{\min}\eta/5$, the range Lemmas 5.3–5.6 work with. (2) The constants $C_1,\dots,C_4$ are chosen after $\delta$ and the $\kappa$ bound but before the rank and incoherence bounds; the thresholds $c_0,\dots,c_3$ and a dimension threshold $d_0\ge 2$ may depend on all three bounds. (3) Noise has $\psi_2$ norm at most $\sigma$ (published Orlicz norm), and the sampling indicators, noise and Gaussian restart vectors are jointly independent. (4) The algorithm steps with choices (eigenvectors, singular vector, pruning) are relations; the good event asserts that an admissible execution exists and that every admissible execution satisfies the bounds; the failure probability is an outer measure. Indices are 0-based and $\log$ is natural.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 8, Theorem 2.4, (12a)–(12b); pp. 19–20, Lemmas 5.3–5.6

import Mathlib
import Definitions.Def_TensorComp_GD_Model

open MeasureTheory

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, Theorem 2.4, p. 8.
The contraction factor is fixed to the value allowed by Lemmas 5.3–5.6. -/
theorem theorem_2_4 :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ κbar : ℝ,
    ∃ C₁ C₂ C₃ C₄ : ℝ,
      0 < C₁ ∧ C₁ < 1 ∧ 0 < C₂ ∧ 0 < C₃ ∧ C₃ < 1 ∧ 0 < C₄ ∧
    ∀ rbar : ℕ, ∀ mubar : ℝ,
    ∃ c₀ c₁ c₃ : ℝ, ∃ c₂ d₀ : ℕ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      2 ≤ d₀ ∧ rbar ≤ d₀ ∧
    ∀ (d r : ℕ) (Ustar : Factor d r) (p σ η : ℝ)
      {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp)
      [IsProbabilityMeasure P]
      (χ : SortedIdx d → Ωp → Bool)
      (E : SortedIdx d → Ωp → ℝ)
      (g : Fin c₂ → Ωp → EuclideanSpace ℝ (Fin d)),
      d₀ ≤ d → 1 ≤ r → r ≤ rbar →
      (∀ s : Fin r, colNorm Ustar s ≠ 0) →
      kappa Ustar ≤ κbar → mu Ustar ≤ mubar →
      0 < p → p ≤ 1 → 0 ≤ σ → Model P p σ χ E g →
      c₀ * Real.log d ^ 4 / (d : ℝ) ^ (3 / 2 : ℝ) ≤ p →
      σ / lamMin Ustar ≤
        c₁ * Real.sqrt p /
          ((d : ℝ) ^ (3 / 4 : ℝ) * Real.log d ^ 2) →
      0 < η →
      η ≤ lamMin Ustar ^ (4 / 3 : ℝ) /
        (32 * lamMax Ustar ^ (8 / 3 : ℝ)) →
      let ρ := 1 - lamMin Ustar ^ (4 / 3 : ℝ) * η / 5
      let epsTh := c₃ *
        (Real.log d / ((d : ℝ) * Real.sqrt p) +
         σ / lamMin Ustar *
           Real.sqrt ((d : ℝ) * Real.log d ^ 2 / p) +
         Real.sqrt (Real.log d / d))
      P {ω | ¬ GoodGD Ustar p σ η epsTh ρ C₁ C₂ C₃ C₄ χ E g ω} ≤
        ENNReal.ofReal δ := by sorry

end TensorComp.GD
