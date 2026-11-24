-- Prove2me | Theorems.Thm_SSLWithoutPairs_stop_gradient_essential
-- name    : SSLWithoutPairs.stop_gradient_essential
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:39:15.314601+00:00
-- url     : https://prove2.me/theorems/67e95d0e-e8e4-432c-9af2-a6ff8d77e4a6
-- title:
--   Theorem 2: the stop-gradient signal is essential for success
-- statement:
--   Under the data model of Lemma 1, with finite second moments and $\eta\ge0$, consider SimSiam ($W_a=W$) without stop-gradient. The objective $J(W)=\tfrac12\mathbb E\|W_pWx_1-Wx_2\|_2^2$ is then differentiated through both branches. Let
--
--   $$H=X'\otimes(W_p^\top W_p+I_{n_2})+X\otimes\tilde W_p^\top\tilde W_p+\eta I_{n_1n_2},\qquad \tilde W_p=W_p-I_{n_2},$$
--
--   where $\otimes$ is the Kronecker product. Then:
--
--   1. For all $W_p,W$, $\ \operatorname{vec}\big(-\partial J/\partial W-\eta W\big)=-H\operatorname{vec}(W)$, so the gradient flow with weight decay reads $\frac{\mathrm d}{\mathrm dt}\operatorname{vec}(W)=-H(t)\operatorname{vec}(W)$.
--   2. $H$ is positive semidefinite for every $W_p$.
--   3. If $W_p(t)$ is any trajectory, $W(t)$ follows $\dot W=-\partial J/\partial W-\eta W$ for $t\ge0$, and $\inf_{t\ge0}\lambda_{\min}(H(t))\ge\lambda_0>0$, then $W(t)\to0$.
--
--   Without the stop-gradient the representation collapses.
--
--   **Formalization Note** $\operatorname{vec}$ stacks columns, so the entry of $\operatorname{vec}(W)$ at index $(j,i)$ is $W_{ij}$. In item 3 the gradient $\partial J/\partial W$ at time $t$ is a matrix $G(t)$, characterised by its partial derivatives.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 2, Theorem 2, eq. (6), p. 3; proof in Appendix A, Theorem 2, eqs. (51)-(56), p. 14

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem stop_gradient_essential {n₁ n₂ : ℕ} (μ : Measure (Fin n₁ → ℝ)) [IsProbabilityMeasure μ]
    (κ : Kernel (Fin n₁ → ℝ) (Fin n₁ → ℝ)) [IsMarkovKernel κ]
    (h2 : ∀ i, Integrable (fun q : (Fin n₁ → ℝ) × (Fin n₁ → ℝ) => q.2 i ^ 2) (μ ⊗ₘ κ))
    (η : ℝ) (hη : 0 ≤ η) :
    (∀ (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) (W : Matrix (Fin n₂) (Fin n₁) ℝ) (i : Fin n₂) (j : Fin n₁),
      HasDerivAt
        (fun s : ℝ => byolLoss μ κ Wp (W + s • Matrix.single i j 1) (W + s • Matrix.single i j 1))
        ((noStopH (augMeanCorr μ κ) (augCov μ κ) η Wp *ᵥ Matrix.vec W) (j, i) - η * W i j) 0) ∧
    (∀ Wp : Matrix (Fin n₂) (Fin n₂) ℝ, (noStopH (augMeanCorr μ κ) (augCov μ κ) η Wp).PosSemidef) ∧
    (∀ (Wp : ℝ → Matrix (Fin n₂) (Fin n₂) ℝ) (W G : ℝ → Matrix (Fin n₂) (Fin n₁) ℝ),
      (∀ t : ℝ, 0 ≤ t → ∀ i j, HasDerivAt
        (fun s : ℝ => byolLoss μ κ (Wp t) (W t + s • Matrix.single i j 1)
          (W t + s • Matrix.single i j 1)) (G t i j) 0) →
      HasMatDerivOn W (fun t => -G t - η • W t) →
      ∀ lam0 : ℝ, 0 < lam0 →
        (∀ t : ℝ, 0 ≤ t → lam0 ≤ minEig (noStopH (augMeanCorr μ κ) (augCov μ κ) η (Wp t))) →
        Tendsto W atTop (𝓝 0)) := by sorry

end SSLWithoutPairs
