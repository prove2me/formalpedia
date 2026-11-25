-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_mul_right_35066f68a6cf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_mul_right_35066f68a6cf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:00.053796+00:00
-- url     : https://prove2.me/theorems/9b993547-5e93-553c-bc82-652551dc06f9
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc mul right 35066f68a6cf: P2 M Ground Theory Heights  Heights Inter mixed Disc mul right 35066f68a6cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc mul right 35066f68a6cf construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc mul right 35066f68a6cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L72-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
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
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_mul_right_35066f68a6cf (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => A k * P) = mixedDisc A * P.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_mul_right» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_mul_right_35066f68a6cf
