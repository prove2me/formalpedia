-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:23.661806+00:00
-- url     : https://prove2.me/theorems/08868468-9c18-4d66-9379-8220b54078a1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem blow Up Of of sub 30a04624d21b: P2 M Ground Theory Heights  Heights Numbers DVR mem blow Up Of of sub 30a04624d21b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem blow Up Of of sub 30a04624d21b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem blow Up Of of sub 30a04624d21b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L76-L85

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j j' : J}
    {a a' : MRing ι R} (h : u j * a - u j' * a' ∈ P) :
    newVar j * liftForm a - newVar j' * liftForm a' ∈ blowUpOf P u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_blowUpOf_of_sub» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
