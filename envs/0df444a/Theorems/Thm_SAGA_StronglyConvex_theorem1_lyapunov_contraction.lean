-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_theorem1_lyapunov_contraction
-- name    : SAGA.StronglyConvex.theorem1_lyapunov_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:26:18.415963+00:00
-- url     : https://prove2.me/theorems/98e7d9a4-cbd7-480a-b2b2-2e155c7d1877
-- title:
--   Theorem 1 — the SAGA Lyapunov function contracts by $1-1/\kappa$ in expectation
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be differentiable with gradients $f_i'$, each $\mu$-strongly convex ($\mu>0$) with $L$-Lipschitz gradient ($L>0$). Let $f=\frac1n\sum_i f_i$, let $h:\mathbb R^d\to\mathbb R$ be convex, and let $x^*$ be a minimizer of $F=f+h$. Set
--
--   $$
--   \gamma=\frac{1}{2(\mu n+L)},\qquad c=\frac{1}{2\gamma(1-\gamma\mu)n},\qquad \kappa=\frac{1}{\gamma\mu},
--   $$
--
--   and let $P=\operatorname{prox}^h_\gamma$, i.e. $P(y)$ minimizes $h(x)+\frac1{2\gamma}\|x-y\|^2$ for every $y$. Let $T$ be the Lyapunov function
--
--   $$
--   T(x,\{\phi_i\})=\frac1n\sum_i f_i(\phi_i)-f(x^*)-\frac1n\sum_i\langle f_i'(x^*),\phi_i-x^*\rangle+c\|x-x^*\|^2 .
--   $$
--
--   Then for every state $(x^k,\{\phi_i^k\})$, if $(x^{k+1},\{\phi_i^{k+1}\})$ is the result of one SAGA iteration with index $j$ drawn uniformly from $\{1,\dots,n\}$,
--
--   $$
--   \mathbb E\big[T^{k+1}\big]\;\le\;\Big(1-\frac1\kappa\Big)T^k .
--   $$
--
--   This one-step contraction is the core of the linear convergence of SAGA; Corollary 1 follows by iterating it.
--
--   **Formalization Note** The inequality is stated for every state $(x,\phi)$, not only for states reachable by SAGA. The expectation is the average $\frac1n\sum_j$ of $T$ at the successor state computed with index $j$ (`Fin n`, 0-based). The constants are hypotheses of the form `γ = 1 / (2 * (μ * n + L))`, `c = 1 / (2 * γ * (1 - γ * μ) * n)`, `κ = 1 / (γ * μ)`, exactly as printed. The proximal operator is any map $P$ with $P(y)$ a minimizer of (3) for all $y$; since that minimizer is unique, $P$ is $\operatorname{prox}^h_\gamma$. $h$ is real-valued, as in the paper.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Theorem 1 (proof pp. 7-8)

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_SAGA_StronglyConvex_sagaStep
import Definitions.Def_SAGA_StronglyConvex_lyapunov

namespace SAGA.StronglyConvex

/-- Theorem 1 (p. 7). Each `f_i` is `μ`-strongly convex with `L`-Lipschitz gradient `f'_i`, `h` is
convex and real-valued, `P` is the proximal map `prox_γ^h` (every `P y` minimizes (3)), and `x*`
(here `xs`) minimizes `F = (1/n) Σ_i f_i + h`. With `γ = 1/(2(μn+L))`, `c = 1/(2γ(1-γμ)n)` and
`κ = 1/(γμ)`, for every state `(x, φ)` the average of the Lyapunov function `T` over the next
SAGA state (index `j` uniform on the `n` components) is at most `(1 - 1/κ) T(x, φ)`. -/
theorem theorem1_lyapunov_contraction {d n : ℕ} (hn : 0 < n)
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
    (γ c κ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L))) (hc : c = 1 / (2 * γ * (1 - γ * μ) * n))
    (hκ : κ = 1 / (γ * μ))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x : EuclideanSpace ℝ (Fin d)) (φ : Fin n → EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' c xs (sagaStep f' P γ (x, φ) j) ≤
      (1 - 1 / κ) * lyapunov f f' c xs (x, φ) := by sorry

end SAGA.StronglyConvex
