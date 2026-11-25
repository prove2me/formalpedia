-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:15.458022+00:00
-- url     : https://prove2.me/theorems/a5f46327-c7e5-5234-9ecf-89bf6ded3b69
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide exists sub component mem 380caf9d8097: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide exists sub component mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide exists sub component mem 380caf9d8097 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide exists sub component mem 380caf9d8097 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L33-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s f : MRing ι F} {n : K → ℕ} (hf : IsMultiHomog f n) (hfL : f ∈ I ⊔ Ideal.span {s}) :
    ∃ t : MRing ι F, f - weightedHomogeneousComponent (blockWeight ι) n (t * s) ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«exists_sub_component_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097
