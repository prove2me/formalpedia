-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_idealMod_mul_D_7cd8f9fb693a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepData_idealMod_mul_D_7cd8f9fb693a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:59.636279+00:00
-- url     : https://prove2.me/theorems/d87a2a59-56d6-426d-9375-4ad99e55553d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Data ideal Mod mul D 7cd8f9fb693a: P2 M Ground Theory Heights  Heights Kleiman Step Data ideal Mod mul D 7cd8f9fb693a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Data ideal Mod mul D 7cd8f9fb693a construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Data ideal Mod mul D 7cd8f9fb693a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L174-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L174-L199

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepData_idealMod_mul_D_7cd8f9fb693a (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepData».«idealMod_mul_D» := P2M_GroundTheory_Heights__Heights_Kleiman_StepData_idealMod_mul_D_7cd8f9fb693a
