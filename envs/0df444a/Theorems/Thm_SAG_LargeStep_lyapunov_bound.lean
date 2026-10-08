-- Prove2me | Theorems.Thm_SAG_LargeStep_lyapunov_bound
-- name    : SAG.LargeStep.lyapunov_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:21.633628+00:00
-- url     : https://prove2.me/theorems/3cffcfca-447d-4f11-9e17-533e084ef128
-- title:
--   §A.6 Step 1 — from y⁰ = 0: EQ(θᵏ) ≤ (1 − 1/(8n))ᵏQ(θ⁰) and Q(θ⁰) = 2(g(x⁰) − g(x*)) + σ²/(nμ)
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Assume $n\ge8L/\mu$ and let $Q$ be the Lyapunov function of §A.6 with $\alpha=\frac1{2n\mu}$, $\eta=2$, $\nu=\frac1{2n}$. Run SAG with step size $\alpha$ and independent uniform indices from $\theta^0=(y^0,x^0)$ with $y^0_1=\dots=y^0_n=0$. Then for every $k\ge0$
--   $$\mathbb EQ(\theta^k)\le\Big(1-\frac1{8n}\Big)^kQ(\theta^0)\qquad\text{and}\qquad Q(\theta^0)=2\big(g(x^0)-g(x^*)\big)+\frac{\sigma^2}{n\mu}.$$
--
--   The first part iterates the one-step contraction; the second evaluates $Q$ at the zero-initialized table.
--
--   **Formalization Note** The expectation is the uniform average over the $n^k$ index sequences.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 28, §A.6 Step 1

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sagRun
import Definitions.Def_SAG_LargeStep_lyapunov

namespace SAG.LargeStep

/-- §A.6 Step 1, p. 28: SAG with `α = 1/(2nμ)` from `θ⁰ = (0, x⁰)`, `nμ/L ≥ 8`:
`EQ(θᵏ) ≤ (1 − 1/(8n))ᵏ Q(θ⁰)` and `Q(θ⁰) = 2(g(x⁰) − g(x*)) + σ²/(nμ)`. -/
theorem lyapunov_bound {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    SAGA.Convex.expectIdx n k (fun js =>
        lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar
          (runFrom f' (1 / (2 * (n : ℝ) * μ)) (fun _ => 0, x0) (List.ofFn js)))
      ≤ (1 - 1 / (8 * (n : ℝ))) ^ k
        * lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar (fun _ => 0, x0)
    ∧ lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar (fun _ => 0, x0)
      = 2 * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)
        + sigmaSq f' xstar / ((n : ℝ) * μ) := by sorry

end SAG.LargeStep
