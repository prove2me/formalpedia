-- Prove2me | Theorems.Thm_StrictCQ_Scaled_Supplement_theorem_6_5
-- name    : StrictCQ.Scaled.Supplement.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:58:28.668469+00:00
-- url     : https://prove2.me/theorems/5d35b212-1bf4-4c22-8894-7d37e31f1c83
-- title:
--   Theorem 6.5 — LAGP-regularity implies Abadie’s constraint qualification
-- statement:
--   Let $C=(h,g)$ have continuously differentiable components on $\mathbb R^n$, and let $x^*\in\Omega=\{x:h(x)=0,\ g(x)\le0\}$. If $x^*$ is LAGP-regular, then Abadie's constraint qualification holds:
--   $$L_\Omega(x^*)=T_\Omega(x^*).$$
--   The linearized cone uses the equality gradients and the inequality gradients active at $x^*$; the tangent cone is the Bouligand tangent cone of the full feasible set. The result identifies the exact tangent geometry under LAGP-regularity and is a companion to the referenced Scaled-AKKT goal.
--
--   **Formalization Note** The conclusion is the published Abadie predicate on the CAKKT constraint structure with exactly the same fields $h,g$. Closedness of $\Omega$ follows from the C¹ assumption and is not an extra premise. The proof's final displayed chain contains a stray polar; the conclusion follows the definition of Abadie on p. 5.
--
--   Differences from the source:
--   - reading: standing C¹ constraints and feasible x* → explicit C.IsC1 and xs ∈ C.feasible; reason: these are inherited from problem (1.1) and Definition 4.4; no extra closedness, compactness or objective is assumed
--   - encoding: one system with Abadie’s CQ → the published CAKKT Abadie predicate applied to the same h and g; reason: its defining equality is exactly L_Ω(x*) = T_Ω(x*) on p. 5; the stray polar in the proof is not part of the stated result
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 24, Theorem 6.5; p. 5, definition of Abadie’s CQ

import Mathlib
import Definitions.Def_StrictCQ_AGP_LAGP
import Definitions.Def_StrictCQ_CAKKT_Setting

namespace StrictCQ.Scaled.Supplement

/-- Theorem 6.5, p. 24: Abadie is equality of the linearized and tangent cones. -/
theorem theorem_6_5 {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hC : C.IsC1) (hxs : xs ∈ C.feasible)
    (hreg : C.LAGPRegular xs) :
    (⟨C.h, C.g⟩ : StrictCQ.CAKKT.Constraints n m p).Abadie xs := by sorry

end StrictCQ.Scaled.Supplement
