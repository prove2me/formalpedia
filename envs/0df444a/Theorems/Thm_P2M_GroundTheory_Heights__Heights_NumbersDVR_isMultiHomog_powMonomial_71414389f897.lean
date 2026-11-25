-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:47.437797+00:00
-- url     : https://prove2.me/theorems/d680cc92-dbd9-46c3-a048-250044327066
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog pow Monomial 71414389f897: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog pow Monomial 71414389f897
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog pow Monomial 71414389f897 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog pow Monomial 71414389f897 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L38-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
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
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897 (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial e i : MRing ι R) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomog_powMonomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897
