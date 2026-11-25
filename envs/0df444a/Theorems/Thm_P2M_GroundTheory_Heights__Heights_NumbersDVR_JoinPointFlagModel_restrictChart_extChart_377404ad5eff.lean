-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_restrictChart_extChart_377404ad5eff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_restrictChart_extChart_377404ad5eff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:06.273352+00:00
-- url     : https://prove2.me/theorems/03563004-9774-5b48-85b6-890ed9dc6426
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model restrict Chart ext Chart 377404ad5eff: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model restrict Chart ext Ch
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model restrict Chart ext Chart 377404ad5eff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model restrict Chart ext Chart 377404ad5eff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointFlagModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel
variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_restrictChart_extChart_377404ad5eff (t : ∀ k, ι k) : restrictChart (extChart t) = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointFlagModel».«restrictChart_extChart» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_restrictChart_extChart_377404ad5eff
