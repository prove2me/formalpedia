-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:25.077466+00:00
-- url     : https://prove2.me/theorems/be716e9c-912f-42f0-9df6-0377777db1cb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial is Multi Homog 630b1c158ab9: P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial is Multi Homog 630b1c158ab9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial is Multi Homog 630b1c158ab9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial is Multi Homog 630b1c158ab9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9 (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial (R := R) e i) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«powMonomial_isMultiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9
