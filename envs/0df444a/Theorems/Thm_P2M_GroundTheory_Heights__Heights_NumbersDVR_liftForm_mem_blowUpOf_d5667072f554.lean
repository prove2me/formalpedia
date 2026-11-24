-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:59.842033+00:00
-- url     : https://prove2.me/theorems/1df31d3e-885e-4152-aa7c-efa8c527e0a4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of d5667072f554: P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of d5667072f554
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of d5667072f554 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of d5667072f554 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L56-L59

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
variable {J : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554 {P : Ideal (MRing ι R)} {u : J → MRing ι R} {p : MRing ι R} (h : p ∈ P) :
    liftForm p ∈ blowUpOf P u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_mem_blowUpOf» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554
