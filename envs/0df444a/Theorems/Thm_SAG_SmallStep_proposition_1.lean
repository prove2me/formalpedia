-- Prove2me | Theorems.Thm_SAG_SmallStep_proposition_1
-- name    : SAG.SmallStep.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:56.299998+00:00
-- url     : https://prove2.me/theorems/f2e5b837-db2a-4f7d-9fdd-a32ae959e532
-- title:
--   Proposition 1 — SAG with $\alpha_k=1/(2nL)$: $\mathbb E\|x^k-x^*\|^2\le(1-\frac{\mu}{8Ln})^k[3\|x^0-x^*\|^2+\frac{9\sigma^2}{4L^2}]$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$, $n\ge1$, be convex and differentiable with gradients $f'_i$ that are Lipschitz continuous with constant $L>0$, $\|f'_i(x)-f'_i(y)\|\le L\|x-y\|$. Assume that the average $g=\frac1n\sum_{i=1}^nf_i$ is strongly convex with constant $\mu>0$, meaning that $x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, and let $x^*$ be the minimizer of $g$. Put $\sigma^2=\frac1n\sum_{i=1}^n\|f'_i(x^*)\|^2$.
--
--   Run the SAG iterations with the constant step size $\alpha_k=\frac1{2nL}$ from $x^0\in\mathbb R^p$ and the zero table $y^0_i=0$ for all $i$, with indices $i_1,i_2,\dots$ independent and uniform on $\{1,\dots,n\}$. Then for every $k\ge1$,
--   $$
--   \mathbb E\big[\|x^k-x^*\|^2\big]\le\Big(1-\frac{\mu}{8Ln}\Big)^k\Big[3\|x^0-x^*\|^2+\frac{9\sigma^2}{4L^2}\Big].
--   $$
--
--   This is the first main result of the paper: an incremental method that evaluates a single component gradient per iteration converges linearly in expectation for strongly convex finite sums, unlike stochastic gradient methods, whose rate is sublinear.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)` and the indices are `Fin n`. The expectation is `SAGA.Convex.expectIdx n k`, the uniform average over all index sequences in $\{1,\dots,n\}^k$, i.e. the law of $k$ i.i.d. uniform indices; the expectation is over the algorithm's randomness only. $x^*$ is a minimizer of $g$ (`∀ x, g x* ≤ g x`); its uniqueness is a consequence. Each $f_i$ is convex as assumed in §A.1 (p. 13) and needed by the proof's co-coercivity step. The run is `SAG.SmallStep.runFrom` with step $1/(2nL)$ from $(0,x^0)$. No restriction $\mu\le L$ is assumed (it follows when $p\ge1$).
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 5, Proposition 1 (standing assumptions p. 5, §3, and p. 13, §A.1; proof pp. 19–23, §A.5)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_SmallStep_run

namespace SAG.SmallStep

/-- Proposition 1 (Le Roux–Schmidt–Bach, arXiv:1202.6258v4, p. 5). With the constant step size
`α = 1/(2nL)` and the table initialized to `y⁰ = 0`, the SAG iterates satisfy, for `k ≥ 1`,
`E‖xᵏ − x*‖² ≤ (1 − μ/(8Ln))ᵏ [3‖x⁰ − x*‖² + 9σ²/(4L²)]`, where `σ² = (1/n) ∑ᵢ ‖f'ᵢ(x*)‖²` and the
expectation is over `k` i.i.d. uniform indices. -/
theorem proposition_1 {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    SAGA.Convex.expectIdx n k
        (fun js => ‖(runFrom f' (1 / (2 * (n : ℝ) * L)) (fun _ => 0, x0) js).2 - xstar‖ ^ 2)
      ≤ (1 - μ / (8 * L * (n : ℝ))) ^ k
        * (3 * ‖x0 - xstar‖ ^ 2 + 9 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2)) := by sorry

end SAG.SmallStep
