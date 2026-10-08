-- Prove2me | Theorems.Thm_SAG_SmallStep_one_step_contraction
-- name    : SAG.SmallStep.one_step_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:28:11.791264+00:00
-- url     : https://prove2.me/theorems/2c8f7840-c779-4637-92a3-b2ee8023c97a
-- title:
--   §A.5 Step 1, p. 22 — with $\alpha=1/(2nL)$, $\delta=\mu/(8nL)$: $\mathbb E[Q(\theta^k)|\mathcal F_{k-1}]\le(1-\delta)Q(\theta^{k-1})$
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients, $L>0$. Assume $g=\frac1n\sum_if_i$ is $\mu$-strongly convex with $\mu>0$, meaning that $x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, and let $x^*$ be the minimizer of $g$. Let $Q$ be the Lyapunov function of §A.5 with step size $\alpha=\frac1{2nL}$ and put $\delta=\frac{\mu}{8nL}$. For every SAG state $\theta^{k-1}$, if $\theta^k$ is the state after one SAG step with step size $\alpha$ and a uniform index,
--   $$
--   \mathbb E[Q(\theta^k)\,|\,\mathcal F_{k-1}]-(1-\delta)Q(\theta^{k-1})\le0 .
--   $$
--
--   This one-step contraction of the Lyapunov function is the heart of Step 1 of the proof of Proposition 1.
--
--   **Formalization Note** The conditional expectation is $\frac1n\sum_iQ(\text{step}_i(\theta))$ for an arbitrary state $\theta$. The inequality $\mu\le L$, which the page uses ("$1-\frac{3\mu}{8L}\ge1-\frac38$"), is not assumed: it follows from the hypotheses when $p\ge1$, and for $p=0$ both sides vanish.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 22, §A.5 Step 1, "Using δ = µ/(8nL) and α = 1/(2nL) gives … Hence, …"

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_SmallStep_run
import Definitions.Def_SAG_SmallStep_blockForm
import Definitions.Def_SAG_SmallStep_lyapunov

namespace SAG.SmallStep

/-- §A.5 Step 1 (arXiv:1202.6258v4, p. 22): with `α = 1/(2nL)` and `δ = μ/(8nL)`,
`E[Q(θᵏ)|F_{k−1}] − (1 − δ)Q(θ^{k−1}) ≤ 0` from any current state `θ`. -/
theorem one_step_contraction {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar
          (step f' (1 / (2 * (n : ℝ) * L)) i θ)
        - (1 - μ / (8 * (n : ℝ) * L)) * lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar θ ≤ 0 := by sorry

end SAG.SmallStep
