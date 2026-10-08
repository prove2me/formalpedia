-- Prove2me | Theorems.Thm_SAG_LargeStep_sag_zero_init_bound
-- name    : SAG.LargeStep.sag_zero_init_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:44.686398+00:00
-- url     : https://prove2.me/theorems/7e52125e-4326-4d5c-a575-eb6488f8524c
-- title:
--   §A.6 Step 2 — SAG from y⁰ = 0, α = 1/(2nμ): E[g(xᵏ) − g(x*)] ≤ (1 − 1/(8n))ᵏ[(7/3)(g(x⁰) − g(x*)) + 7σ²/(6nμ)]
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Assume $n\ge8L/\mu$. Run SAG with step size $\alpha=\frac1{2n\mu}$ and independent uniform indices from $x^0$ with all $y^0_i=0$. Then for every $k\ge0$
--   $$\mathbb E\big[g(x^k)-g(x^*)\big]\le\Big(1-\frac1{8n}\Big)^k\Big[\frac73\big(g(x^0)-g(x^*)\big)+\frac{7\sigma^2}{6n\mu}\Big].$$
--
--   This is the convergence of SAG without warm start; Proposition 2 applies it from the averaged stochastic gradient iterate.
--
--   **Formalization Note** The page writes "$\mathbb E[g(x^k)-g(x^*)]\le2\mathbb EQ(\theta^k)$"; the domination $Q\ge\frac67(g-g^*)$ gives the factor $\frac76$, and the printed bracket $\frac73(g(x^0)-g(x^*))+\frac{7\sigma^2}{6n\mu}=\frac76\big[2(g(x^0)-g(x^*))+\frac{\sigma^2}{n\mu}\big]$ is the one that factor produces. The statement is that bracket, which is what the proof establishes.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 30, §A.6 Step 2, first display

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sagRun

namespace SAG.LargeStep

/-- §A.6 Step 2, p. 30, first display (constant as the proof establishes it): SAG with
`α = 1/(2nμ)` from `(y⁰, x⁰) = (0, x⁰)`, `nμ/L ≥ 8`:
`E[g(xᵏ) − g(x*)] ≤ (1 − 1/(8n))ᵏ [(7/3)(g(x⁰) − g(x*)) + 7σ²/(6nμ)]`. -/
theorem sag_zero_init_bound {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    SAGA.Convex.expectIdx n k (fun js =>
        SAGA.Convex.fAvg f (runFrom f' (1 / (2 * (n : ℝ) * μ)) (fun _ => 0, x0) (List.ofFn js)).2
          - SAGA.Convex.fAvg f xstar)
      ≤ (1 - 1 / (8 * (n : ℝ))) ^ k
        * (7 / 3 * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)
          + 7 * sigmaSq f' xstar / (6 * (n : ℝ) * μ)) := by sorry

end SAG.LargeStep
