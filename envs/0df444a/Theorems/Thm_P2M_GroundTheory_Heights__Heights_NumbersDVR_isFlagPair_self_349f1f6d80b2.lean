-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_self_349f1f6d80b2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_self_349f1f6d80b2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:29.218193+00:00
-- url     : https://prove2.me/theorems/7ac9aecc-a952-4be4-8893-9d7e50ceca5a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair self 349f1f6d80b2: P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair self 349f1f6d80b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair self 349f1f6d80b2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair self 349f1f6d80b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L190-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L190-L202

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_self_349f1f6d80b2 (ϖ : O) (y : (Σ k, ι k) → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) :
    IsFlagPair ϖ y (scaledTrivBundle O (segreVec y) r hs) (scaledTrivBundle O (segreVec y) r hs)
      (scaledBasis r hs) (scaledBasis r hs) 0 0 (fun _ => 1) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isFlagPair_self» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_self_349f1f6d80b2
