-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:32.896956+00:00
-- url     : https://prove2.me/theorems/d6b16690-4ded-4c0e-a2a8-914611a197ab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Data is Unit D 53d41fd9d7c5: P2 M Ground Theory Heights  Heights Kleiman Step Data is Unit D 53d41fd9d7c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Data is Unit D 53d41fd9d7c5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Data is Unit D 53d41fd9d7c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L163-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L163-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5 (I : Chart x) : IsUnit (T.D.sub I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepData».«isUnit_D» := P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5
