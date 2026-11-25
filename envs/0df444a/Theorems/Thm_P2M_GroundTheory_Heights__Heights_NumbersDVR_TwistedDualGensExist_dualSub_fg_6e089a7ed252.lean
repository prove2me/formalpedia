-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:06.879125+00:00
-- url     : https://prove2.me/theorems/6cbdd163-ed94-4725-8bde-3c95ada68200
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist dual Sub fg 6e089a7ed252: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist dual Sub fg 6e089a7ed252
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist dual Sub fg 6e089a7ed252 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist dual Sub fg 6e089a7ed252 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L106-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L106-L146

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252 [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.dualSub B c).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«dualSub_fg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252
