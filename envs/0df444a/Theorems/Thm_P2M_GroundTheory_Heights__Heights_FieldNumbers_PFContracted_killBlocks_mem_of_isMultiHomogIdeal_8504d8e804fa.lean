-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:36.397316+00:00
-- url     : https://prove2.me/theorems/7339a49c-0ad5-43b0-9294-23fbbf7b447e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks mem of is Multi Homog Ideal 8504d8e804fa: P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks mem of i
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks mem of is Multi Homog Ideal 8504d8e804fa construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks mem of is Multi Homog Ideal 8504d8e804fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L121-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa {Q : Ideal (MRing ι F)} (hQ : IsMultiHomogIdeal Q)
    (T : Finset K) {q : MRing ι F} (hq : q ∈ Q) : killBlocks T q ∈ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«killBlocks_mem_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
