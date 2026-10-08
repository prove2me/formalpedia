-- Prove2me | Theorems.Thm_SAGA_Convex_prox_svrg_inequality
-- name    : SAGA.Convex.prox_svrg_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:44:03.079006+00:00
-- url     : https://prove2.me/theorems/198e3422-f2e6-4f53-814a-344e67d3ab69
-- title:
--   Appendix C — the prox-SVRG inequality for one SAGA step
-- statement:
--   Let $n\ge1$ and $L>0$. Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients $f_i'$, $f=\frac1n\sum_i f_i$, let $h:\mathbb R^d\to\mathbb R$ be convex, $F=f+h$, and let $x^*$ minimize $F$. Run SAGA with step $\gamma=\frac1{3L}$ and $P=\mathrm{prox}^h_\gamma$. For every state $(x^k,\phi^k)$ and every $\alpha>0$, with $x^{k+1}$ the next iterate, $\Delta$ the gradient error of the step, and $\mathbb E$ the average over the index $j$ drawn uniformly from $\{1,\dots,n\}$,
--
--   $$
--   \alpha\,\mathbb E\|x^{k+1}-x^*\|^2\le\alpha\|x^k-x^*\|^2-2\alpha\gamma\,\mathbb E\big[F(x^{k+1})-F(x^*)\big]+2\alpha\gamma^2\,\mathbb E\|\Delta\|^2 .
--   $$
--
--   This is the inequality of Xiao and Zhang for proximal SVRG, transferred to SAGA; the paper cites it rather than proving it. It produces the term $-2\alpha\gamma\,\mathbb E[F(x^{k+1})-F(x^*)]$ that drives the $O(n/k)$ rate of Theorem 2.
--
--   **Formalization Note** $P$ is any map with $P(y)$ a minimizer of $h(z)+\frac1{2\gamma}\|z-y\|^2$ for every $y$, which for convex $h$ is $\mathrm{prox}^h_\gamma$. $\mathbb E$ is written as $\frac1n\sum_j$.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, Appendix C, p. 12, first display (citing Xiao & Zhang, prox-SVRG, 2nd eq. on p. 12)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep

namespace SAGA.Convex

/-- Appendix C, p. 12 (the prox-SVRG inequality of Xiao–Zhang, applied to SAGA): each `fᵢ`
convex with `L`-Lipschitz gradient, `h` convex, `x*` a minimizer of `F = f + h`, step
`γ = 1/(3L)`, `P = prox_γ^h`. For every state `(x^k, φ^k)` and every `α > 0`, with `E` the
average over the uniformly drawn index `j`,
`α E‖x^{k+1} - x*‖² ≤ α ‖x^k - x*‖² - 2αγ E[F(x^{k+1}) - F(x*)] + 2αγ² E‖Δ‖²`. -/
theorem prox_svrg_inequality {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    {α : ℝ} (hα : 0 < α)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    α * ((1 / (n : ℝ)) * ∑ j, ‖(sagaStep f' P (1 / (3 * L)) s j).1 - xs‖ ^ 2) ≤
      α * ‖s.1 - xs‖ ^ 2
        - 2 * α * (1 / (3 * L)) * ((1 / (n : ℝ)) * ∑ j,
            ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
              - (fAvg f xs + h xs)))
        + 2 * α * (1 / (3 * L)) ^ 2 *
            ((1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' (1 / (3 * L)) s j‖ ^ 2) := by sorry

end SAGA.Convex
