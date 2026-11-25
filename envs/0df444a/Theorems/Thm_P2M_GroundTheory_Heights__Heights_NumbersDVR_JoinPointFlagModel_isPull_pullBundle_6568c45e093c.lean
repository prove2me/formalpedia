-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_isPull_pullBundle_6568c45e093c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_isPull_pullBundle_6568c45e093c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:08.370851+00:00
-- url     : https://prove2.me/theorems/a3d4a074-5cff-4f86-bd05-cb6e28e638df
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model is Pull pull Bundle 6568c45e093c: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model is Pull pull Bundle 6568c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model is Pull pull Bundle 6568c45e093c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model is Pull pull Bundle 6568c45e093c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L85-L94

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
variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_isPull_pullBundle_6568c45e093c (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    IsPull O y (ptCoord (Ω := Ω)) B (pullBundle O y B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointFlagModel».«isPull_pullBundle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_isPull_pullBundle_6568c45e093c
