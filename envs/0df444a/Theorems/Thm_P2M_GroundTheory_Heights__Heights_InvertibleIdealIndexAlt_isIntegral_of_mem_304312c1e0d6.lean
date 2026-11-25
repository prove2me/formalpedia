-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_isIntegral_of_mem_304312c1e0d6
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_isIntegral_of_mem_304312c1e0d6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:17.315112+00:00
-- url     : https://prove2.me/theorems/fd6ec7c7-ccb3-5152-a646-11d80306e606
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt is Integral of mem 304312c1e0d6: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt is Integral of mem 304312c1e0d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt is Integral of mem 304312c1e0d6 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt is Integral of mem 304312c1e0d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L75-L77

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_isIntegral_of_mem_304312c1e0d6 {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    IsIntegral ℤ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«isIntegral_of_mem» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_isIntegral_of_mem_304312c1e0d6
