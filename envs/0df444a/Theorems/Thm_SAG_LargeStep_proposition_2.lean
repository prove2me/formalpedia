-- Prove2me | Theorems.Thm_SAG_LargeStep_proposition_2
-- name    : SAG.LargeStep.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:22.059871+00:00
-- url     : https://prove2.me/theorems/740e7b72-09e5-45e9-9139-0ce3ef0669dd
-- title:
--   Proposition 2 — for n ≥ 8L/μ, SAG with α = 1/(2nμ) after an SG pass satisfies E[g(xᵏ) − g(x*)] ≤ C(1 − 1/(8n))ᵏ for k ≥ n
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Assume $n\ge\frac{8L}{\mu}$. Consider the run in which the first $n$ iterations use stochastic gradient from $x^0$ with step sizes $\gamma_j=1/(2L+\frac\mu2j)$, SAG is then initialized with the average $x^n=\frac1n\sum_{j=0}^{n-1}\tilde x^j$ of the stochastic gradient iterates and with all $y_i$ set to zero, and the subsequent SAG iterations use step size $\alpha_k=\frac1{2n\mu}$; all indices are independent and uniform on $\{1,\dots,n\}$. Then for every $k\ge n$
--   $$\mathbb E\big[g(x^k)-g(x^*)\big]\le C\Big(1-\frac1{8n}\Big)^k,\qquad C=\frac{16L}{3n}\|x^0-x^*\|^2+\frac{4\sigma^2}{3n\mu}\Big(8\log\Big(1+\frac{\mu n}{4L}\Big)+1\Big).$$
--
--   The paper explains: "We state this result for $k\ge n$ because we assume that the first $n$ iterations of the algorithm use an SG method and that we initialize the subsequent SAG iterations with the average of the iterates, which leads to an $O((\log n)/k)$ rate. In contrast, using the SAG iterations from the beginning gives the same rate but with a constant proportional to $n$. Note that this bound is obtained when initializing all $y_i$ to zero after the SG phase."
--
--   When $n\ge8L/\mu$, each pass through the data thus reduces the expected suboptimality by the factor $(1-\frac1{8n})^n\le e^{-1/8}$, independently of $\mu$ and $L$.
--
--   **Formalization Note** The run is `hybrid` (see its definition for the index bookkeeping: $k$ indices are drawn, the stochastic gradient phase uses the first $n-1$, index $n$ is unused, SAG uses the last $k-n$). The expectation is the uniform average over all $n^k$ index sequences.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 6, Proposition 2 (and the paragraph after it); proof pp. 14–15 (§A.3), 23–30 (§A.6)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_hybrid

namespace SAG.LargeStep

/-- Proposition 2, p. 6: if `n ≥ 8L/μ`, the run of `hybrid` (one pass of stochastic gradient
with `γ_j = 1/(2L + μj/2)`, average of its iterates, table reset to `0`, then SAG with
`α = 1/(2nμ)`) satisfies, for `k ≥ n`, `E[g(xᵏ) − g(x*)] ≤ C (1 − 1/(8n))ᵏ` with
`C = 16L/(3n)‖x⁰ − x*‖² + 4σ²/(3nμ)(8 log(1 + μn/(4L)) + 1)`. -/
theorem proposition_2 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ)) (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : n ≤ k) :
    SAGA.Convex.expectIdx n k (fun js =>
        SAGA.Convex.fAvg f (hybrid f' L μ x0 js) - SAGA.Convex.fAvg f xstar)
      ≤ (16 * L / (3 * (n : ℝ)) * ‖x0 - xstar‖ ^ 2
          + 4 * sigmaSq f' xstar / (3 * (n : ℝ) * μ)
            * (8 * Real.log (1 + μ * (n : ℝ) / (4 * L)) + 1))
        * (1 - 1 / (8 * (n : ℝ))) ^ k := by sorry

end SAG.LargeStep
