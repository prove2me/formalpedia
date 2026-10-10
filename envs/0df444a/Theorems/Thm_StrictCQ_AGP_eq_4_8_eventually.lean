-- Prove2me | Theorems.Thm_StrictCQ_AGP_eq_4_8_eventually
-- name    : StrictCQ.AGP.eq_4_8_eventually
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:35.143961+00:00
-- url     : https://prove2.me/theorems/60e02125-da39-489d-8e85-1f65bedbcb41
-- title:
--   (4.8), proof of Theorem 4.2, p. 8 — for k large, N_{Ω(xᵏ,γ)}(xᵏ + εᵏ) ⊂ N_{Ω(xᵏ,−∞)}(xᵏ + εᵏ)
-- statement:
--   Let the constraint functions be $\mathrm C^1$, $x^*$ feasible, and $\gamma\in[-\infty,0)$. Let $x^k\to x^*$ and $\varepsilon^k\to0$ with $x^k+\varepsilon^k\in\Omega(x^k,\gamma)$ for all $k$. Then for all sufficiently large $k$,
--
--   $$
--   N_{\Omega(x^k,\gamma)}(x^k+\varepsilon^k)\subset N_{\Omega(x^k,-\infty)}(x^k+\varepsilon^k).
--   $$
--
--   This inclusion lets the proof of Theorem 4.2 pass from AGP($\gamma$) for an arbitrary $\gamma<0$ to the cones $N_{\Omega(x,-\infty)}$ that define AGP-regularity.
--
--   **Formalization Note** The paper says the inclusion "always holds". For finite $\gamma$ that is not literally true: the point $x^k+\varepsilon^k$ may violate a row $g_j(x^k)+\langle\nabla g_j(x^k),\varepsilon^k\rangle\le0$ with $g_j(x^k)\le\gamma$, which belongs to $\Omega(x^k,-\infty)$ but not to $\Omega(x^k,\gamma)$; the right-hand normal cone is then empty while the left one contains $0$. Such rows have $g_j(x^*)\le\gamma<0$, so the inclusion does hold for $k$ large, which is all the proof uses. The statement is therefore "eventually".
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 8, (4.8), proof of Theorem 4.2

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- (4.8), for `k` large: if `xᵏ → xs`, `εᵏ → 0` and `xᵏ + εᵏ ∈ Ω(xᵏ, γ)` with `γ < 0`, then
eventually `N_{Ω(xᵏ,γ)}(xᵏ + εᵏ) ⊆ N_{Ω(xᵏ,-∞)}(xᵏ + εᵏ)`. -/
theorem eq_4_8_eventually {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (γ : EReal) (hγ : γ < 0)
    (x ε : ℕ → EuclideanSpace ℝ (Fin n)) (hx : Tendsto x atTop (𝓝 xs))
    (hε : Tendsto ε atTop (𝓝 0)) (hy : ∀ k, x k + ε k ∈ C.linSet (x k) γ) :
    ∀ᶠ k in atTop,
      normalCone (C.linSet (x k) γ) (x k + ε k) ⊆
        normalCone (C.linSet (x k) ⊥) (x k + ε k) := by sorry

end StrictCQ.AGP
