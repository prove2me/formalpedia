-- Prove2me | Theorems.Thm_StrictCQ_Scaled_Supplement_limNormal_subset_polar_linCone
-- name    : StrictCQ.Scaled.Supplement.limNormal_subset_polar_linCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:57:55.443821+00:00
-- url     : https://prove2.me/theorems/0380652e-b172-4845-83d4-29a629b298b0
-- title:
--   Proof of Theorem 6.5 — limiting normals lie in the polar linearized cone
-- statement:
--   Let $C=(h,g)$ have continuously differentiable components on $\mathbb R^n$, and let $x^*\in\Omega=\{x:h(x)=0,\ g(x)\le0\}$. If $x^*$ is LAGP-regular, then the Mordukhovich limiting normal cone is contained in the polar of the linearized cone:
--   $$N_\Omega(x^*)\subseteq L_\Omega(x^*)^\circ.$$
--   Here $N_\Omega$ is the outer limit, along feasible points, of the Fréchet regular normal cones. This is the principal inclusion established in the proof of Theorem 6.5.
--
--   **Formalization Note** LAGP-regularity retains its domain restriction $x\in\Omega_L$, with unrestricted perturbations in $\mathbb R^n$. The conclusion uses the limiting normal cone, not the convex normal cone.
--
--   Differences from the source:
--   - reading: standing C¹ constraints and feasible x* → explicit C.IsC1 and xs ∈ C.feasible; reason: these are the same governing assumptions as Theorem 6.5
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 24, proof of Theorem 6.5

import Mathlib
import Definitions.Def_StrictCQ_AGP_LAGP
import Definitions.Def_StrictCQ_CAKKT_Setting

namespace StrictCQ.Scaled.Supplement

/-- The main inclusion in the proof of Theorem 6.5, p. 24, under LAGP-regularity. -/
theorem limNormal_subset_polar_linCone {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hC : C.IsC1) (hxs : xs ∈ C.feasible)
    (hreg : C.LAGPRegular xs) :
    StrictCQ.CAKKT.limNormal C.feasible xs ⊆ StrictCQ.AGP.polar (C.linCone xs) := by sorry

end StrictCQ.Scaled.Supplement
