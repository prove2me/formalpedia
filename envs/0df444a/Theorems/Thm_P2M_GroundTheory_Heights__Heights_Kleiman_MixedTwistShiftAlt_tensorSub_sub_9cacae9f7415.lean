-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_tensorSub_sub_9cacae9f7415
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_tensorSub_sub_9cacae9f7415
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:48.610737+00:00
-- url     : https://prove2.me/theorems/328925e6-304c-4776-bf0e-3353dd5f5339
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt tensor Sub sub 9cacae9f7415: P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt tensor Sub sub 9cacae9f7415
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt tensor Sub sub 9cacae9f7415 construction uses the P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt tensor Sub sub 9cacae9f7415 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L38-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PMixedTwistShift
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShiftAlt
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_tensorSub_sub_9cacae9f7415 {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«MixedTwistShiftAlt».«tensorSub_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_tensorSub_sub_9cacae9f7415
