-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:25.915321+00:00
-- url     : https://prove2.me/theorems/329021e5-4f84-52c7-993a-b9d2c36e0f56
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted coeff kill Blocks 263d92e57432: P2 M Ground Theory Heights  Heights Field Numbers PFContracted coeff kill Blocks 263d92e57432
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted coeff kill Blocks 263d92e57432 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted coeff kill Blocks 263d92e57432 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L73-L85

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432 (T : Finset K) (q : MRing ι F) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killBlocks T q) = if ∀ v ∈ d.support, v.1 ∉ T then coeff d q else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«coeff_killBlocks» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432
