-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:12.750851+00:00
-- url     : https://prove2.me/theorems/f1ad25f9-58b0-4179-b816-942ab6f69f98
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks monomial ab5dd46129ab: P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks monomial ab5dd46129ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks monomial ab5dd46129ab construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted kill Blocks monomial ab5dd46129ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L59-L71

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab (T : Finset K) (d : (Σ k, ι k) →₀ ℕ) (c : F) :
    killBlocks T (monomial d c) =
      if ∀ v ∈ d.support, v.1 ∉ T then monomial d c else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«killBlocks_monomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab
