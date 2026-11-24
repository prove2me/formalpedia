-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:52.069299+00:00
-- url     : https://prove2.me/theorems/6e6ef6c2-7e7d-44d6-aa11-a41cd9051dba
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists form separator d6cdd5665e0a: P2 M Ground Theory Heights  Heights Numbers DVR exists form separator d6cdd5665e0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists form separator d6cdd5665e0a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists form separator d6cdd5665e0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L73-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L73-L88

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a {H : Ideal (MRing ι R)} [hH : H.IsPrime]
    (S : Finset (Ideal (MRing ι R))) (hS : ∀ H' ∈ S, IsMultiHomogIdeal H' ∧ ¬ H' ≤ H) :
    ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ H ∧ ∀ H' ∈ S, a ∈ H' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_form_separator» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a
