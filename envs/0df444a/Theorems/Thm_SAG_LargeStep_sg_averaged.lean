-- Prove2me | Theorems.Thm_SAG_LargeStep_sg_averaged
-- name    : SAG.LargeStep.sg_averaged
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:07.898802+00:00
-- url     : https://prove2.me/theorems/6bdc8654-46f8-4285-bfa4-c07e6a32e792
-- title:
--   §A.3 — averaged SG iterate: E g((1/k)∑x̃ⁱ) − g(x*) ≤ (2L/k)‖x⁰ − x*‖² + (4σ²/(kμ)) log(1 + μk/(4L))
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Run stochastic gradient from $\tilde x^0=x^0$ with step sizes $\gamma_j=1/(2L+\frac\mu2 j)$ and independent uniform indices. Then for every $k\ge1$
--   $$\mathbb E\,g\Big(\frac1k\sum_{i=0}^{k-1}\tilde x^i\Big)-g(x^*)\le\frac{2L}{k}\|x^0-x^*\|^2+\frac{4\sigma^2}{k\mu}\log\Big(1+\frac{\mu k}{4L}\Big).$$
--
--   With $k=n$ this bounds the starting point of the SAG phase in Proposition 2 and produces the logarithmic term of its constant.
--
--   **Formalization Note** The expectation is over $k$ independent uniform indices; the averaged points $\tilde x^0,\dots,\tilde x^{k-1}$ use only the first $k-1$ of them. The page's chain contains two misprints (a stray factor $L$ in "$\frac{2L}{k}L\|x^0-x^*\|^2$" and $\mathbb Eg(x^{k-1})$ for $\mathbb Eg(x^i)$ in the first line); the statement is the chain's last line, without them.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 15, §A.3, last display

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sgRun

namespace SAG.LargeStep

/-- §A.3, p. 15, last display: with `γ_j = 1/(2L + μj/2)` and `k ≥ 1`,
`E g((1/k) ∑_{i=0}^{k−1} x̃ⁱ) − g(x*) ≤ (2L/k)‖x⁰ − x*‖² + (4σ²/(kμ)) log(1 + μk/(4L))`. -/
theorem sg_averaged {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    SAGA.Convex.expectIdx n k (fun js => SAGA.Convex.fAvg f
        ((1 / (k : ℝ)) • ∑ i ∈ Finset.range k, sgIterate f' (sgStepSize L μ) x0 js i))
      - SAGA.Convex.fAvg f xstar
      ≤ 2 * L / (k : ℝ) * ‖x0 - xstar‖ ^ 2
        + 4 * sigmaSq f' xstar / ((k : ℝ) * μ) * Real.log (1 + μ * (k : ℝ) / (4 * L)) := by sorry

end SAG.LargeStep
