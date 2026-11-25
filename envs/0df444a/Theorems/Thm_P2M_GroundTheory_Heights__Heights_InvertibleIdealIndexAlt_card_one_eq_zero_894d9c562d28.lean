-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:04.8405+00:00
-- url     : https://prove2.me/theorems/dbea94f9-3e1a-4e46-b706-7d0d5a4a752c
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt card one eq zero 894d9c562d28: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt card one eq zero 894d9c562d28
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt card one eq zero 894d9c562d28 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt card one eq zero 894d9c562d28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L166-L171

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

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28 [NumberField L] : Nat.card (1 : Submodule (𝓞 L) L).toAddSubgroup = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«card_one_eq_zero» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28
