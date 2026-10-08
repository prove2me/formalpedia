-- Prove2me | Theorems.Thm_SAGA_Convex_saga_averaged_iterate_rate
-- name    : SAGA.Convex.saga_averaged_iterate_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:01:32.495316+00:00
-- url     : https://prove2.me/theorems/bb16e762-d48d-475a-9d17-441ca39d037d
-- title:
--   Theorem 2 — SAGA's $4n/k$ rate for the averaged iterate without strong convexity
-- statement:
--   Let $n\ge1$ and $L>0$. Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients $f_i'$, let $f=\frac1n\sum_i f_i$ with gradient $f'=\frac1n\sum_i f_i'$, let $h:\mathbb R^d\to\mathbb R$ be convex, $F=f+h$, and let $x^*$ be a minimizer of $F$. Run SAGA from $x^0$ (table $\phi_i^0=x^0$) with step size $\gamma=\frac1{3L}$ and proximal map $\mathrm{prox}^h_\gamma$, the indices $j^1,j^2,\dots$ being independent and uniform on $\{1,\dots,n\}$. Then for every $k\ge1$, with $\bar x^k=\frac1k\sum_{t=1}^k x^t$,
--
--   $$
--   \mathbb E\big[F(\bar x^k)\big]-F(x^*)\le\frac{4n}{k}\Big[\frac{2L}{n}\|x^0-x^*\|^2+f(x^0)-\langle f'(x^*),x^0-x^*\rangle-f(x^*)\Big],
--   $$
--
--   where the expectation is over the indices $j^1,\dots,j^k$.
--
--   This is the sublinear $O(n/k)$ guarantee of SAGA for composite problems that are convex but not strongly convex: the same method, without knowledge of a strong convexity constant, converges in function value of the averaged iterate.
--
--   **Formalization Note** The proximal operator enters as a map $P$ with $P(y)$ a minimizer of $h(z)+3L\|z-y\|^2/2$ for every $y$. The expectation is the uniform average over the $n^k$ index sequences `Fin k → Fin n`; $x^t$ uses the first $t$ indices. The bracket on the right uses $f$ and $f'$, not $F$, as printed. $h$ is real-valued (no indicator functions).
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, Appendix C, p. 11, Theorem 2 (announced on p. 2)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_sagaRun

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- Theorem 2 (Appendix C, p. 11): each `fᵢ` convex with `L`-Lipschitz gradient, `h` convex,
`x*` a minimizer of `F = f + h`, SAGA run with `γ = 1/(3L)` and `P = prox_γ^h` from `x^0`
(with `φᵢ^0 = x^0`). For every `k ≥ 1`, with `x̄^k = (1/k) ∑_{t=1}^k x^t` and `E` over the `k`
independent uniform indices,
`E[F(x̄^k)] - F(x*) ≤ (4n/k) [(2L/n)‖x^0 - x*‖² + f(x^0) - ⟨f′(x*), x^0 - x*⟩ - f(x*)]`. -/
theorem saga_averaged_iterate_rate {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k) :
    expectIdx n k (fun js => fAvg f (avgIterate f' P (1 / (3 * L)) x0 js)
        + h (avgIterate f' P (1 / (3 * L)) x0 js))
      - (fAvg f xs + h xs) ≤
      4 * n / k * (2 * L / n * ‖x0 - xs‖ ^ 2 + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫
        - fAvg f xs) := by sorry

end SAGA.Convex
