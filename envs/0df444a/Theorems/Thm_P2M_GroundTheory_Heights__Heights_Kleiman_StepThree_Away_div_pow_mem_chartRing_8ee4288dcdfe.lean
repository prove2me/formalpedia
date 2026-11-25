-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:42.392609+00:00
-- url     : https://prove2.me/theorems/869e9932-e61c-4f4b-ac6a-b98c6ba3d3ef
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away div pow mem chart Ring 8ee4288dcdfe: P2 M Ground Theory Heights  Heights Kleiman Step Three Away div pow mem chart Ring 8ee4288dcdfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away div pow mem chart Ring 8ee4288dcdfe construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away div pow mem chart Ring 8ee4288dcdfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L92-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {h : Poly S N} {d : ℕ}
    (hh : h.IsHomogeneous d) : aeval x h / x i ^ d ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«div_pow_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe
