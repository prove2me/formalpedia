-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:23.168752+00:00
-- url     : https://prove2.me/theorems/fc8e6754-aa5f-4d08-a642-bc30900d6466
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight block Deg b5265fab4acc: P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight block Deg b5265fab4acc
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight block Deg b5265fab4acc construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight block Deg b5265fab4acc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L24-L26

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc (k : K) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockDeg (ι := ι) k) d = Finsupp.weight (blockWeight ι) d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«weight_blockDeg» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc
