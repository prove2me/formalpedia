-- Prove2me | Theorems.Thm_SAGA_Convex_lyapunov_one_step
-- name    : SAGA.Convex.lyapunov_one_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:44:19.87566+00:00
-- url     : https://prove2.me/theorems/29d1cefc-12f7-475c-b010-5b25b1b3b51e
-- title:
--   Appendix C — one-step decrease of the Lyapunov function, $\gamma=1/(3L)$
-- statement:
--   Let $n\ge1$ and $L>0$. Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients, $f=\frac1n\sum_i f_i$, $h:\mathbb R^d\to\mathbb R$ convex, $F=f+h$, and $x^*$ a minimizer of $F$. Run SAGA with $\gamma=\frac1{3L}$ and $P=\mathrm{prox}^h_\gamma$, and let $T$ be the Lyapunov function
--
--   $$
--   T(x,\phi)=\frac1n\sum_i f_i(\phi_i)-f(x^*)-\frac1n\sum_i\langle f_i'(x^*),\phi_i-x^*\rangle+(c+\alpha)\|x-x^*\|^2,\qquad c=\frac{3L}{2n},\ \alpha=\frac{3L}{8n}.
--   $$
--
--   Then for every state $(x^k,\phi^k)$, writing $T^k=T(x^k,\phi^k)$, $T^{k+1}$ for $T$ at the next state and $\mathbb E$ for the average over the index $j$ drawn uniformly from $\{1,\dots,n\}$,
--
--   $$
--   \mathbb E[T^{k+1}]-T^k\le-\frac1{4n}\,\mathbb E\big[F(x^{k+1})-F(x^*)\big].
--   $$
--
--   Telescoping this inequality over $k$ steps gives Theorem 2.
--
--   **Formalization Note** The coefficient of $\|x-x^*\|^2$ is written $\frac{3L}{2n}+\frac{3L}{8n}$. $\mathbb E$ is the conditional expectation given the state, written $\frac1n\sum_j$.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, Appendix C, p. 12, display after "We thus obtain"

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_lyapunov

namespace SAGA.Convex

/-- Appendix C, p. 12 (one-step decrease): each `fᵢ` convex with `L`-Lipschitz gradient, `h`
convex, `x*` a minimizer of `F = f + h`, step `γ = 1/(3L)`, `P = prox_γ^h`, and the Lyapunov
function `T` with coefficient `c + α = 3L/(2n) + 3L/(8n)` on `‖x - x*‖²`. For every state
`(x^k, φ^k)`, with `E` the average over the uniformly drawn index `j`,
`E[T^{k+1}] - T^k ≤ -(1/(4n)) E[F(x^{k+1}) - F(x*)]`. -/
theorem lyapunov_one_step {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n))
        (sagaStep f' P (1 / (3 * L)) s j)
      - lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n)) s ≤
      -(1 / (4 * (n : ℝ))) * ((1 / (n : ℝ)) * ∑ j,
          ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
            - (fAvg f xs + h xs))) := by sorry

end SAGA.Convex
