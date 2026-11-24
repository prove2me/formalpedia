-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:40.664949+00:00
-- url     : https://prove2.me/theorems/cdbb94f6-f5b1-44fe-9444-e5c85b746807
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Proj Prime bot dfd17cf75014: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Proj Prime bot dfd17cf75014
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Proj Prime bot dfd17cf75014 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Proj Prime bot dfd17cf75014 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L127-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014 {R : Type*} [CommRing R] [IsDomain R] [∀ k, Nonempty (ι k)] :
    IsMultiProjPrime (⊥ : Ideal (MRing ι R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiProjPrime_bot» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014
