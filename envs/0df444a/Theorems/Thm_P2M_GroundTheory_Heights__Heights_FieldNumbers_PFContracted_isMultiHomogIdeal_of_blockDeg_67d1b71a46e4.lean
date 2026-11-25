-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:14.25999+00:00
-- url     : https://prove2.me/theorems/5582aca5-40e7-41a0-ab30-3c433cd945ec
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal of block Deg 67d1b71a46e4: P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal of bl
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal of block Deg 67d1b71a46e4 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal of block Deg 67d1b71a46e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L60-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L60-L99

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4 [Fintype K] {I : Ideal (MRing ι F)}
    (h : ∀ (k : K) (n : ℕ), ∀ r ∈ I, weightedHomogeneousComponent (blockDeg k) n r ∈ I) :
    IsMultiHomogIdeal I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«isMultiHomogIdeal_of_blockDeg» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_blockDeg_67d1b71a46e4
