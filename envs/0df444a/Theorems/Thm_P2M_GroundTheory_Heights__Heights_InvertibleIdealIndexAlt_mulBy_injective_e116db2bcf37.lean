-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:08.653663+00:00
-- url     : https://prove2.me/theorems/3d98a6a6-a885-491f-9eed-dc14b7119c94
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul By injective e116db2bcf37: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul By injective e116db2bcf37
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul By injective e116db2bcf37 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt mul By injective e116db2bcf37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L23-L24

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37 {c : L} (hc : c ≠ 0) : Function.Injective (mulBy c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«mulBy_injective» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37
