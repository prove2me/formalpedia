-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_eq_4dac95f2f9a9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_eq_4dac95f2f9a9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:04.117971+00:00
-- url     : https://prove2.me/theorems/aaf7c519-86a4-4493-b481-f814575c11c0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form C eq 4dac95f2f9a9: P2 M Ground Theory Heights  Heights Numbers DVR lift Form C eq 4dac95f2f9a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form C eq 4dac95f2f9a9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form C eq 4dac95f2f9a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L27-L28

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_eq_4dac95f2f9a9 {J : Type} (a : R) : liftForm (ι := ι) (J := J) (C a : MRing ι R) = C a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_C_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_eq_4dac95f2f9a9
