-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:52.121811+00:00
-- url     : https://prove2.me/theorems/f1238587-b16d-465b-b782-e30e3d1cab67
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists form not mem of is Relevant 8f453759efa5: P2 M Ground Theory Heights  Heights Numbers DVR exists form not mem of is Relevant 8f453759efa5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists form not mem of is Relevant 8f453759efa5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists form not mem of is Relevant 8f453759efa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L90-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L90-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5 [Fintype K] {H : Ideal (MRing ι R)} [hH : H.IsPrime]
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_form_not_mem_of_isRelevant» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5
