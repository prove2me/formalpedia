-- Prove2me | Theorems.Thm_SAGA_Convex_delta_second_moment
-- name    : SAGA.Convex.delta_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:43:33.872977+00:00
-- url     : https://prove2.me/theorems/0acebf67-7417-4542-aa31-60816323113b
-- title:
--   Appendix C — second-moment bound for the SAGA gradient error $\Delta$
-- statement:
--   Let $n\ge1$, let $f_1',\dots,f_n':\mathbb R^d\to\mathbb R^d$ be arbitrary maps, $f'=\frac1n\sum_i f_i'$, $\gamma>0$ and $\beta>0$. Fix a SAGA state $(x^k,\phi^k)$ and a point $x^*$. For the index $j$, let $w_j^{k+1}$ be the SAGA gradient step (eq. (1)) and $\Delta_j=-\frac1\gamma(w_j^{k+1}-x^k)-f'(x^k)$. With $\mathbb E$ the average over $j$ uniform on $\{1,\dots,n\}$,
--
--   $$
--   \mathbb E\|\Delta\|^2\le(1+\beta^{-1})\,\mathbb E\|f_j'(\phi_j^k)-f_j'(x^*)\|^2+(1+\beta)\,\mathbb E\|f_j'(x^k)-f_j'(x^*)\|^2 .
--   $$
--
--   In the proof of Theorem 2 this bounds the last term of the prox-SVRG inequality in terms of quantities controlled by the Lyapunov function.
--
--   **Formalization Note** $\mathbb E$ is written as $\frac1n\sum_j$ over `Fin n`. No property of the maps $f_i'$ is needed.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, Appendix C, p. 12, display after "To bound the Delta term" (Delta defined on p. 11)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaStep

namespace SAGA.Convex

/-- Appendix C, p. 12 (the bound on `Δ`): for every state `(x^k, φ^k)`, every point `x*`, every
step `γ > 0` and every `β > 0`, with `Δ_j = -(1/γ)(w^{k+1}_j - x^k) - f′(x^k)` and `E` the average
over the uniformly drawn index `j`,
`E‖Δ‖² ≤ (1 + β⁻¹) E‖f′_j(φ_j^k) - f′_j(x*)‖² + (1 + β) E‖f′_j(x^k) - f′_j(x*)‖²`. -/
theorem delta_second_moment {d n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' γ s j‖ ^ 2 ≤
      (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖f' j (s.2 j) - f' j xs‖ ^ 2)
        + (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖f' j s.1 - f' j xs‖ ^ 2) := by sorry

end SAGA.Convex
