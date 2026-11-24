-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:14.150599+00:00
-- url     : https://prove2.me/theorems/0a818476-aa6f-4855-a9a8-479770e791b0
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt rel Index map subtype 1ba93abccb64: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt rel Index map subtype 1ba93abccb64
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt rel Index map subtype 1ba93abccb64 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt rel Index map subtype 1ba93abccb64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L122-L129

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64 (B : Subring L) (H : AddSubgroup B) :
    (H.map B.subtype.toAddMonoidHom).relIndex B.toAddSubgroup = H.index := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«relIndex_map_subtype» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64
