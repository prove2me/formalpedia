-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:36.514799+00:00
-- url     : https://prove2.me/theorems/e734977d-3467-4b2b-b18f-0be3fa64c70f
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq ba0dcb3ccb8a: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq ba0dcb3ccb8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq ba0dcb3ccb8a construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq ba0dcb3ccb8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L131-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a (B : Subring L) (β : B) :
    B.toAddSubgroup.map (mulBy (β : L)) =
      (Ideal.span {β}).toAddSubgroup.map B.subtype.toAddMonoidHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«map_mul_eq» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
