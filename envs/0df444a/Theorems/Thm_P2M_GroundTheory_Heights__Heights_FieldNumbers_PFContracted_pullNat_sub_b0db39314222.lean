-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:15.411088+00:00
-- url     : https://prove2.me/theorems/5ab3a9a7-c3f2-45a6-b7ef-59bec62ece93
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat sub b0db39314222: P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat sub b0db39314222
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat sub b0db39314222 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat sub b0db39314222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L234-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L234-L245

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
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222 (b : K → ℤ) :
    (fun k' => (pullNat K K' j (fun κ => (b κ).toNat) k' : ℤ) -
      pullNat K K' j (fun κ => (-b κ).toNat) k') = pullDeg j b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«pullNat_sub» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222
