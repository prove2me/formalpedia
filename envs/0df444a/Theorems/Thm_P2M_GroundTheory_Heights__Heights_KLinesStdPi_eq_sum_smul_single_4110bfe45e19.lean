-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19
-- name    : P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:45.674947+00:00
-- url     : https://prove2.me/theorems/4e3a1bca-c8eb-4194-aaa2-1470f6a86389
-- title:
--   P2 M Ground Theory Heights  Heights KLines Std Pi eq sum smul single 4110bfe45e19: P2 M Ground Theory Heights  Heights KLines Std Pi eq sum smul single 4110bfe45e19
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Std Pi eq sum smul single 4110bfe45e19 construction uses the P2 M Ground Theory Heights  Heights KLines Std Pi eq sum smul single 4110bfe45e19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesStdPi.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesStdPi.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdPi
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
open GroundTheory.Heights₂.Heights.KLinesStdPi

theorem P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19 {K : Type*} [Field K] {k : ℕ} (y : Fin k → 𝓞 K) :
    (fun i => algebraMap (𝓞 K) K (y i)) = ∑ j, y j • (Pi.single j 1 : Fin k → K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesStdPi».«eq_sum_smul_single» := P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19
