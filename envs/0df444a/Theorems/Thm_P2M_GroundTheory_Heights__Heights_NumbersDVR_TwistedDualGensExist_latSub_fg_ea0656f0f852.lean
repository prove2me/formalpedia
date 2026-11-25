-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:00.85324+00:00
-- url     : https://prove2.me/theorems/21bcc97f-6817-476b-bd9d-e49b976cc14f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist lat Sub fg ea0656f0f852: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist lat Sub fg ea0656f0f852
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist lat Sub fg ea0656f0f852 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist lat Sub fg ea0656f0f852 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L52-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L52-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852 {x : τ → Ω} (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.latSub B c).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«latSub_fg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852
