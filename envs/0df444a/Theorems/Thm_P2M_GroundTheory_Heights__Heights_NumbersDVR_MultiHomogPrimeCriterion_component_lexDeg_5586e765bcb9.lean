-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_component_lexDeg_5586e765bcb9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_component_lexDeg_5586e765bcb9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:44.344797+00:00
-- url     : https://prove2.me/theorems/1c290727-f006-5165-ba41-c80881df9ddc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion component lex Deg 5586e765bcb9: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion component lex De
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion component lex Deg 5586e765bcb9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion component lex Deg 5586e765bcb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_component_lexDeg_5586e765bcb9 (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (lexDeg ∘ blockWeight ι) (lexDeg b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«component_lexDeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_component_lexDeg_5586e765bcb9
