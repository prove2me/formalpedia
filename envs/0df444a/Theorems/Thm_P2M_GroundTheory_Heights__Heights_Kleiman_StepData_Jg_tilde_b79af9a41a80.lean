-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_Jg_tilde_b79af9a41a80
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepData_Jg_tilde_b79af9a41a80
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:43.868298+00:00
-- url     : https://prove2.me/theorems/0fa29a84-a02d-46d2-8151-cd6801ddb12d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Data Jg tilde b79af9a41a80: P2 M Ground Theory Heights  Heights Kleiman Step Data Jg tilde b79af9a41a80
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Data Jg tilde b79af9a41a80 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Data Jg tilde b79af9a41a80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L145-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L145-L161

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepData_Jg_tilde_b79af9a41a80 (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepData».«Jg_tilde» := P2M_GroundTheory_Heights__Heights_Kleiman_StepData_Jg_tilde_b79af9a41a80
