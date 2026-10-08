-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_corollary1_linear_convergence
-- name    : SAGA.StronglyConvex.corollary1_linear_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:44:58.365992+00:00
-- url     : https://prove2.me/theorems/fae0978a-fd60-4134-9523-99afbcbdcbe8
-- title:
--   Corollary 1 — linear convergence of SAGA under strong convexity: $\mathbb E\|x^k-x^*\|^2\le(1-\frac{\mu}{2(\mu n+L)})^k[\dots]$
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be differentiable with gradients $f_i'$, each $\mu$-strongly convex ($\mu>0$) with $L$-Lipschitz gradient ($L>0$). Let $f=\frac1n\sum_i f_i$ with gradient $f'=\frac1n\sum_i f_i'$, let $h:\mathbb R^d\to\mathbb R$ be convex, and let $x^*$ be a minimizer of the composite objective $F=f+h$. Run SAGA with step size
--
--   $$
--   \gamma=\frac{1}{2(\mu n+L)}
--   $$
--
--   and proximal operator $\operatorname{prox}^h_\gamma$, starting from $x^0$ with $\phi_i^0=x^0$ for all $i$, the index at each iteration drawn independently and uniformly from $\{1,\dots,n\}$. Then for every $k\ge0$,
--
--   $$
--   \mathbb E\,\|x^k-x^*\|^2\;\le\;\Big(1-\frac{\mu}{2(\mu n+L)}\Big)^k\Big[\|x^0-x^*\|^2+\frac{n}{\mu n+L}\big(f(x^0)-\langle f'(x^*),x^0-x^*\rangle-f(x^*)\big)\Big],
--   $$
--
--   where the expectation is over all choices of the indices up to step $k$.
--
--   This is the linear convergence rate of SAGA in the strongly convex composite case, which contains the non-composite case $h=0$. Note that $x^*$ minimizes $f+h$, so $f'(x^*)$ need not vanish; the bracket uses $f$, not $F$.
--
--   **Formalization Note** The expectation is the average over all $n^k$ index sequences $j_1,\dots,j_k$ (functions `Fin k → Fin n`) of $\|x^k-x^*\|^2$, where $x^k$ is the deterministic SAGA run along that sequence; this is exactly the expectation under $k$ independent uniform indices. The proximal operator is any map $P$ with $P(y)$ a minimizer of $h(x)+\frac1{2\gamma}\|x-y\|^2$ for every $y$, which by uniqueness is $\operatorname{prox}^h_\gamma$. $h$ is real-valued, as the paper types it; a minimizer $x^*$ of $F$ is assumed to exist. Indices are 0-based.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 8, Corollary 1 (announced on p. 2, Section 2)

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_SAGA_StronglyConvex_sagaRun

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Corollary 1 (p. 8; announced on p. 2): linear convergence of SAGA in the strongly convex
composite case. Each `f_i` is `μ`-strongly convex with `L`-Lipschitz gradient `f'_i`, `h` is convex
and real-valued, `P` is the proximal map `prox_γ^h`, `x*` (here `xs`) minimizes
`F = f + h` with `f = (1/n) Σ_i f_i`, and `γ = 1/(2(μn+L))`. SAGA starts at `x^0` with
`φ_i^0 = x^0`. The expectation over the `k` indices, drawn independently and uniformly from the
`n` components, is the average over all `n^k` index sequences. -/
theorem corollary1_linear_convergence {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2 ≤
      (1 - μ / (2 * (μ * n + L))) ^ k *
        (‖x0 - xs‖ ^ 2 + n / (μ * n + L) *
          ((1 / (n : ℝ)) * ∑ i, f i x0 - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x0 - xs⟫_ℝ
            - (1 / (n : ℝ)) * ∑ i, f i xs)) := by sorry

end SAGA.StronglyConvex
