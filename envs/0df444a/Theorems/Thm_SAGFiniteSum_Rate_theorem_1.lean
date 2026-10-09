-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_theorem_1
-- name    : SAGFiniteSum.Rate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:12.036979+00:00
-- url     : https://prove2.me/theorems/c5a3ca52-20a4-468b-93d6-df9c67fb47e3
-- title:
--   Theorem 1, p. 7 — SAG with α = 1/(16L): E[g(x̄ᵏ)] − g(x*) ≤ (32n/k)C₀, and E[g(xᵏ)] − g(x*) ≤ (1 − min{μ/16L, 1/8n})ᵏC₀ if g is μ-strongly convex
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$, $n\ge1$, be convex and differentiable with gradients $f'_i$ that are Lipschitz continuous with constant $L>0$, $\|f'_i(x)-f'_i(y)\|\le L\|x-y\|$, and let $x^*$ be a minimizer of $g=\frac1n\sum_{i=1}^nf_i$. Put $g'=\frac1n\sum_if'_i$ and $\sigma^2=\frac1n\sum_i\|f'_i(x^*)\|^2$.
--
--   Run the stochastic average gradient (SAG) method with the constant step size $\alpha_k=\frac1{16L}$ from $x^0\in\mathbb R^p$: at iteration $k$ an index $i_k$ is drawn uniformly from $\{1,\dots,n\}$, independently of the past, the table entry $y_{i_k}$ is replaced by $f'_{i_k}(x^{k-1})$, and $x^k=x^{k-1}-\frac{\alpha}{n}\sum_iy^k_i$. Let $\bar x^k=\frac1k\sum_{i=0}^{k-1}x^i$. Then for every $k\ge1$,
--   $$
--   \mathbb E\big[g(\bar x^k)\big]-g(x^*)\ \le\ \frac{32n}{k}\,C_0,
--   $$
--   where
--   1. if the table is initialized with $y^0_i=0$, then $C_0=g(x^0)-g(x^*)+\frac{4L}n\|x^0-x^*\|^2+\frac{\sigma^2}{16L}$;
--   2. if it is initialized with $y^0_i=f'_i(x^0)-g'(x^0)$, then $C_0=\frac32\big[g(x^0)-g(x^*)\big]+\frac{4L}n\|x^0-x^*\|^2$.
--
--   Further, if $g$ is $\mu$-strongly convex for some $\mu>0$ (that is, $x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex), then for each of the two initializations, with its $C_0$,
--   $$
--   \mathbb E\big[g(x^k)\big]-g(x^*)\ \le\ \Big(1-\min\Big\{\frac{\mu}{16L},\frac1{8n}\Big\}\Big)^kC_0 .
--   $$
--
--   This is the main result of the paper: SAG, which evaluates one component gradient per iteration, attains the $O(1/k)$ rate of full gradient descent in the convex case and a linear rate in the strongly convex case, with constants that make it faster than both stochastic and deterministic gradient methods for large $n$.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)` and indices are `Fin n`. The expectation over the algorithm's randomness is `SAGA.Convex.expectIdx n k`, the uniform average over all $n^k$ index sequences; the data are deterministic. The four claims (two initializations, two rates) are stated as one conjunction; strong convexity is a hypothesis of the last two only. The theorem covers every $n\ge1$, including $n=1$, where SAG is gradient descent and the page's proof does not apply (it assumes $n>1$).
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, §3, Theorem 1, p. 7

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- Theorem 1 (Schmidt, Le Roux & Bach, arXiv:1309.2388v2, p. 7). SAG with the constant step
size `α = 1/(16L)`, for `k ≥ 1`, from `(y⁰, x⁰)` with `y⁰ = 0` or `y⁰ᵢ = f'ᵢ(x⁰) − g'(x⁰)`:
`E[g(x̄ᵏ)] − g(x*) ≤ (32n/k) C₀`, and if `g` is `μ`-strongly convex,
`E[g(xᵏ)] − g(x*) ≤ (1 − min{μ/(16L), 1/(8n)})ᵏ C₀`, with the `C₀` of each initialization. -/
theorem theorem_1 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0centered f L xstar x0)) := by sorry

end SAGFiniteSum.Rate
