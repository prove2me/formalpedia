-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:00.600263+00:00
-- url     : https://prove2.me/theorems/158b5b0b-a3a7-4e17-8668-53e1800b9949
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of mono 79a813d4a6e9: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of mono 79a813d4a6e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of mono 79a813d4a6e9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of mono 79a813d4a6e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L20-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalStrict
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9 {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpOf_mono» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9
