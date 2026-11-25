-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:14.380872+00:00
-- url     : https://prove2.me/theorems/a68685d3-3fca-4db0-8144-9a2c5e4cdf28
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight apply eq zero iff 311ff90258dd: P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight apply eq zero iff 311ff90258
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight apply eq zero iff 311ff90258dd construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted weight apply eq zero iff 311ff90258dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L87-L98

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = 0 ↔ ∀ v ∈ d.support, v.1 ≠ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«weight_apply_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd
