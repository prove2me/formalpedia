-- Prove2me | Theorems.Thm_SSLWithoutPairs_byol_gradient
-- name    : SSLWithoutPairs.byol_gradient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:37:09.507044+00:00
-- url     : https://prove2.me/theorems/1ae9f1dd-a72a-42e9-afea-fdb46823ef23
-- title:
--   Lemma 1: BYOL learning dynamics (gradient of the stop-gradient objective)
-- statement:
--   Let $x\in\mathbb R^{n_1}$ have law $p$ and let $p_{\mathrm{aug}}(\cdot\mid x)$ be an augmentation distribution with finite second moments, $\mathbb E\|x'\|_2^2<\infty$ for $x\sim p$, $x'\sim p_{\mathrm{aug}}(\cdot\mid x)$. Let $x_1,x_2\sim p_{\mathrm{aug}}(\cdot\mid x)$ be independent given $x$. Let $X=\mathbb E[\bar x\bar x^\top]$ with $\bar x(x)=\mathbb E_{x'\sim p_{\mathrm{aug}}(\cdot|x)}[x']$, and $X'=\mathbb E_x[\operatorname{Var}_{x'\mid x}[x']]$. For
--
--   $$J(W,W_p)=\tfrac12\,\mathbb E\,\|W_pWx_1-\mathrm{StopGrad}(W_ax_2)\|_2^2,$$
--
--   with $W,W_a\in\mathbb R^{n_2\times n_1}$ and $W_p\in\mathbb R^{n_2\times n_2}$, the partial derivatives with $W_a$ held fixed are
--
--   $$-\frac{\partial J}{\partial W_p}=\big(-W_pW(X+X')+W_aX\big)W^\top,\qquad -\frac{\partial J}{\partial W}=W_p^\top\big(-W_pW(X+X')+W_aX\big).$$
--
--   The BYOL flows (2)-(3) are these negative gradients, the predictor one scaled by $\alpha_p$, plus weight decay $-\eta W_p$, $-\eta W$.
--
--   **Formalization Note** The stop-gradient is encoded by passing $W_a$ as a separate argument of $J$, so differentiation in $W$ does not reach the target branch. Each partial derivative $\partial J/\partial w_{ij}$ is stated as the derivative at $s=0$ of $s\mapsto J(W+sE_{ij})$. The printed main-text Lemma 1 already includes $\alpha_p$ and $\eta$; these are modelling choices rather than consequences of $J$, so the statement is the gradient computation of Appendix A, Lemma 1.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 2, Lemma 1, eqs. (1)-(3), p. 3; Appendix A, Lemma 1, eqs. (20)-(22), p. 12

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem byol_gradient {n₁ n₂ : ℕ} (μ : Measure (Fin n₁ → ℝ)) [IsProbabilityMeasure μ]
    (κ : Kernel (Fin n₁ → ℝ) (Fin n₁ → ℝ)) [IsMarkovKernel κ]
    (h2 : ∀ i, Integrable (fun q : (Fin n₁ → ℝ) × (Fin n₁ → ℝ) => q.2 i ^ 2) (μ ⊗ₘ κ))
    (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : Matrix (Fin n₂) (Fin n₁) ℝ) :
    (∀ i j, HasDerivAt (fun s : ℝ => byolLoss μ κ (Wp + s • Matrix.single i j 1) W Wa)
      (-(byolFlowWp 1 0 (augMeanCorr μ κ) (augCov μ κ) Wp W Wa) i j) 0) ∧
    (∀ i j, HasDerivAt (fun s : ℝ => byolLoss μ κ Wp (W + s • Matrix.single i j 1) Wa)
      (-(byolFlowW 0 (augMeanCorr μ κ) (augCov μ κ) Wp W Wa) i j) 0) := by sorry

end SSLWithoutPairs
