-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:21.723237+00:00
-- url     : https://prove2.me/theorems/3b52dc6a-e0e5-4a3f-ab56-aa46f3b2b98a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion weight lex Deg 0fa8b812e0c3: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion weight lex Deg 0fa8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion weight lex Deg 0fa8b812e0c3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion weight lex Deg 0fa8b812e0c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L43-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3 (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«weight_lexDeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3
