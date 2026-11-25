-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:26.556807+00:00
-- url     : https://prove2.me/theorems/ee3871c7-2102-4507-b17f-276026bb3712
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class List map Domain 596b3c63997b: P2 M Ground Theory Heights  Heights Numbers DVR class List map Domain 596b3c63997b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class List map Domain 596b3c63997b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class List map Domain 596b3c63997b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L83-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
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
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b {σ τ : Type*} (cls : τ → K → ℤ) (φ : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (μ.mapDomain φ) = classList (cls ∘ φ) μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classList_mapDomain» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b
