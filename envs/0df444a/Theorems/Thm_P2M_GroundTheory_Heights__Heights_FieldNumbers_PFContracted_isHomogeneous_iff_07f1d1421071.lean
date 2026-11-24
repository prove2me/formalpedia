-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:22.927139+00:00
-- url     : https://prove2.me/theorems/17a487bc-16a4-4189-8608-2e3db8fa4ce3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Homogeneous iff 07f1d1421071: P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Homogeneous iff 07f1d1421071
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Homogeneous iff 07f1d1421071 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Homogeneous iff 07f1d1421071 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L28-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071 {M : Type*} [AddCommMonoid M] [DecidableEq M] (w : (Σ k, ι k) → M)
    (I : Ideal (MRing ι F)) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F w) ↔
      ∀ (m : M), ∀ r ∈ I, weightedHomogeneousComponent w m r ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«isHomogeneous_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071
