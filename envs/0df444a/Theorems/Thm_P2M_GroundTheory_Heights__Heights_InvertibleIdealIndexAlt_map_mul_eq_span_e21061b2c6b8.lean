-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:31.951796+00:00
-- url     : https://prove2.me/theorems/e226d2b3-2219-45d8-b9bf-0b39fc39eb8e
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq span e21061b2c6b8: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq span e21061b2c6b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq span e21061b2c6b8 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt map mul eq span e21061b2c6b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L143-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L143-L164

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8 [NumberField L] {B : Subring L} [Module.Finite ℤ B] (β : B) :
    (1 : Submodule (𝓞 L) L).toAddSubgroup.map (mulBy (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B))).toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«map_mul_eq_span» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
