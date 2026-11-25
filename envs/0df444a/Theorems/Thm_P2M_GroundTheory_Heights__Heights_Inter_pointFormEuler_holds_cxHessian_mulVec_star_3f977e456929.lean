-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:59.730186+00:00
-- url     : https://prove2.me/theorems/db89abf6-2479-4f4e-abce-5e74ad998ae9
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds cx Hessian mul Vec star 3f977e456929: P2 M Ground Theory Heights  Heights Inter point Form Euler holds cx Hessian mul Vec star 3f977e45
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds cx Hessian mul Vec star 3f977e456929 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds cx Hessian mul Vec star 3f977e456929 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L52-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L52-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929 (f : (Fin n → ℂ) → ℝ) (y x : Fin n → ℂ) (i : Fin n) :
    (cxHessian f y *ᵥ star x) i = leviOf (fderiv ℝ (fderiv ℝ f) y) (Pi.single i 1) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«cxHessian_mulVec_star» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929
