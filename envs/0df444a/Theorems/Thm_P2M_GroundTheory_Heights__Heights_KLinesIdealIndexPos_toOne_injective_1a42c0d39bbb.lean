-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:06.085051+00:00
-- url     : https://prove2.me/theorems/adb96cca-a461-4d74-a9d9-20c948502cdb
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Index Pos to One injective 1a42c0d39bbb: P2 M Ground Theory Heights  Heights KLines Ideal Index Pos to One injective 1a42c0d39bbb
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Index Pos to One injective 1a42c0d39bbb construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Index Pos to One injective 1a42c0d39bbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealIndexPos.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealIndexPos.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos
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
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb : Function.Injective (toOne K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealIndexPos».«toOne_injective» := P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb
