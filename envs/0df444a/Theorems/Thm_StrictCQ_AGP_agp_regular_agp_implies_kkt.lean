-- Prove2me | Theorems.Thm_StrictCQ_AGP_agp_regular_agp_implies_kkt
-- name    : StrictCQ.AGP.agp_regular_agp_implies_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:23.17638+00:00
-- url     : https://prove2.me/theorems/2d189a20-1343-4a5d-b563-3f751ecd3ed9
-- title:
--   (4.7)–(4.9), proof of Theorem 4.2, pp. 7–8 — under AGP-regularity, AGP(γ) implies KKT for every γ ∈ [−∞, 0)
-- statement:
--   Let the constraint functions of (1.1) be $\mathrm C^1$ and let $x^*$ be a feasible point at which AGP-regularity holds. Let $\gamma\in[-\infty,0)$ and let $f$ be a $\mathrm C^1$ objective for which AGP($\gamma$) holds at $x^*$. Then
--
--   $$
--   \text{the KKT condition holds at } x^* \text{ for } f.
--   $$
--
--   This is the first half of Theorem 4.2: AGP-regularity is a strict constraint qualification for AGP, uniformly in the parameter $\gamma$.
--
--   **Formalization Note** KKT is in multiplier form. Stating the result for every $\gamma\in[-\infty,0)$ avoids the $\gamma$-independence of AGP proved in Martínez–Svaiter, which is not part of this paper.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 7–8, (4.7)–(4.9), proof of Theorem 4.2

import Mathlib
import Definitions.Def_StrictCQ_AGP_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- (4.7)–(4.9): under AGP-regularity, AGP(γ) for any `γ ∈ [-∞, 0)` implies KKT. -/
theorem agp_regular_agp_implies_kkt {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (hreg : C.AGPRegular xs)
    (γ : EReal) (hγ : γ < 0) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hagp : C.AGP γ f xs) :
    C.IsKKT f xs := by sorry

end StrictCQ.AGP
