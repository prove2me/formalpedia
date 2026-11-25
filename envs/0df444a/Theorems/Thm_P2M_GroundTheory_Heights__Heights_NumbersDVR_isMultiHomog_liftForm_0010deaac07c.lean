-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:03.005799+00:00
-- url     : https://prove2.me/theorems/ca24f255-6c4f-4cf4-8389-c6db7caf0506
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog lift Form 0010deaac07c: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog lift Form 0010deaac07c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog lift Form 0010deaac07c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog lift Form 0010deaac07c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L19-L36

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c {J : Type} {p : MRing ι R} {c : K → ℕ} (h : IsMultiHomog p c) :
    IsMultiHomog (liftForm (J := J) p) (liftMDeg c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomog_liftForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c
