-- Prove2me | Theorems.Thm_Sqrt6KissingBound_preimage_strictCone_linearIsometryEquiv
-- name    : Sqrt6KissingBound.preimage_strictCone_linearIsometryEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:52.619073+00:00
-- url     : https://prove2.me/theorems/6e395349-f939-4a8c-bc2b-5cb2d1dddc85
-- title:
--   Sqrt6 Kissing Bound: preimage strict Cone linear Isometry Equiv
-- statement:
--   Linear isometries transport strict cones.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Geometry.lean#L31-L36
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Geometry.lean#L31-L36

import Mathlib
import Definitions.Def_Sqrt6KissingBound_Geometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Sqrt6KissingBound.preimage_strictCone_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) {x z : E}
    (hAx : A x = z) : A ⁻¹' strictCone z = strictCone x := by sorry
