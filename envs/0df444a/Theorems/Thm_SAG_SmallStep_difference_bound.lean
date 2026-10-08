-- Prove2me | Theorems.Thm_SAG_SmallStep_difference_bound
-- name    : SAG.SmallStep.difference_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:53.050165+00:00
-- url     : https://prove2.me/theorems/12882ebc-81c5-4009-b459-3c516c701bab
-- title:
--   §A.5 Step 1, p. 21 — for $\delta\le1/(3n)$, the bound on $\mathbb E[Q(\theta^k)|\mathcal F_{k-1}]-(1-\delta)Q(\theta^{k-1})$
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients $f'_i$, $L>0$. Let $g=\frac1n\sum_if_i$ and let $x^*$ be a minimizer of $g$. Let $\alpha>0$, let $Q$ be the Lyapunov function of §A.5 with step size $\alpha$, and let $0\le\delta\le\frac1{3n}$. For every SAG state $\theta^{k-1}=(y^{k-1},x^{k-1})$, if $\theta^k$ is the state after one SAG step with step size $\alpha$ and a uniform index,
--   $$
--   \mathbb E[Q(\theta^k)\,|\,\mathcal F_{k-1}]-(1-\delta)Q(\theta^{k-1})
--   \le-(2\alpha-3\alpha^2nL)(x^{k-1}-x^*)^\top g'(x^{k-1})
--   +\left(\delta-\frac{\delta^2\big(1-\frac1n\big)^2}{\big[3n\delta-1-2\delta+\frac{\delta-1}{n}\big]}\,n\right)\|x^{k-1}-x^*\|^2 .
--   $$
--   The bracket $3n\delta-1-2\delta+\frac{\delta-1}{n}$ is negative for $\delta\le\frac1{3n}$.
--
--   This is the one-step estimate of the proof of Proposition 1 before strong convexity is used; it holds for every positive step size.
--
--   **Formalization Note** The conditional expectation is $\frac1n\sum_i Q(\text{step}_i(\theta))$ for an arbitrary current state $\theta$. $x^*$ is a minimizer of $g$ (`∀ x, g x* ≤ g x`); $g'(x^*)=0$ is a consequence. The page requires $\delta>0$ for its purpose; the bound is stated for $0\le\delta\le\frac1{3n}$, the page's sufficient condition.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 21, §A.5 Step 1, last display

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_SmallStep_run
import Definitions.Def_SAG_SmallStep_blockForm
import Definitions.Def_SAG_SmallStep_lyapunov

open scoped RealInnerProductSpace

namespace SAG.SmallStep

/-- §A.5 Step 1 (arXiv:1202.6258v4, last display of p. 21): for every step size `α > 0` and
every `0 ≤ δ ≤ 1/(3n)`, the one-step difference `E[Q(θᵏ)|F_{k−1}] − (1 − δ)Q(θ^{k−1})` of the
Lyapunov function of §A.5, from any current state `θ = (y^{k−1}, x^{k−1})`. -/
theorem difference_bound {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (α : ℝ) (hα : 0 < α) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (3 * (n : ℝ)))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, lyapunov f' α xstar (step f' α i θ)
        - (1 - δ) * lyapunov f' α xstar θ
      ≤ -(2 * α - 3 * α ^ 2 * (n : ℝ) * L) * ⟪θ.2 - xstar, SAGA.Convex.gradAvg f' θ.2⟫
        + (δ - δ ^ 2 * (1 - 1 / (n : ℝ)) ^ 2
            / (3 * (n : ℝ) * δ - 1 - 2 * δ + (δ - 1) / (n : ℝ)) * (n : ℝ))
          * ‖θ.2 - xstar‖ ^ 2 := by sorry

end SAG.SmallStep
