-- Prove2me | Theorems.Thm_SAG_LargeStep_lyapunov_dominates
-- name    : SAG.LargeStep.lyapunov_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:18.85673+00:00
-- url     : https://prove2.me/theorems/6607cc96-ecfb-4add-89c9-0eea6ecf784b
-- title:
--   §A.6 Step 2 — Q(y, x) ≥ (63/64)(g(x) − g(x*)) for every state, when nμ/L ≥ 8
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Assume $\mu/L\ge8/n$ and let $Q$ be the Lyapunov function of §A.6 with $\alpha=\frac1{2n\mu}$, $\eta=2$, $\nu=\frac1{2n}$. Then for every state $\theta=(y,x)$
--   $$Q(\theta)\ge\frac{63}{64}\big(g(x)-g(x^*)\big).$$
--
--   In particular $Q(\theta)\ge\frac67(g(x)-g(x^*))$, which is how the paper uses it: the decay of $\mathbb EQ(\theta^k)$ transfers to the suboptimality $\mathbb E[g(x^k)-g(x^*)]$.
--
--   **Formalization Note** The paper's chain ends with $\frac{63}{64}$ and then $\frac67$; the statement keeps the sharper $\frac{63}{64}$, from which $\frac67$ follows.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, pp. 28–29, §A.6 Step 2

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_lyapunov

namespace SAG.LargeStep

/-- §A.6 Step 2, p. 29: with `α = 1/(2nμ)`, `η = 2`, `ν = 1/(2n)` and `μ/L ≥ 8/n`, for every
state `θ = (y, x)`: `Q(θ) ≥ (63/64)(g(x) − g(x*))` (hence `≥ (6/7)(g(x) − g(x*))`). -/
theorem lyapunov_dominates {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    63 / 64 * (SAGA.Convex.fAvg f θ.2 - SAGA.Convex.fAvg f xstar)
      ≤ lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar θ := by sorry

end SAG.LargeStep
