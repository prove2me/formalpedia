-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_monoSmall_5eb05c0d4637
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_monoSmall_5eb05c0d4637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:28.006699+00:00
-- url     : https://prove2.me/theorems/1d865e66-4bfc-4a2b-9c06-a1d84674a6ef
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename mono Small 5eb05c0d4637: P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename mono Small 5eb05c0d4637
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename mono Small 5eb05c0d4637 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted rename mono Small 5eb05c0d4637 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L252-L254

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
variable {F K K' j ι'}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_monoSmall_5eb05c0d4637 (i : ∀ k', ι' k') (e : K → ℕ) :
    rename (blockIncl j ι') (monoSmall (F := F) i e) = ∏ κ, X ⟨j κ, i (j κ)⟩ ^ e κ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«rename_monoSmall» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_monoSmall_5eb05c0d4637
