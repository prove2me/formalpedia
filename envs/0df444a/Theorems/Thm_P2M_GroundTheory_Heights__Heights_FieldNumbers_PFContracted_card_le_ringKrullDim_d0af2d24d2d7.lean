-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_card_le_ringKrullDim_d0af2d24d2d7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_card_le_ringKrullDim_d0af2d24d2d7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:00.332807+00:00
-- url     : https://prove2.me/theorems/7c4b83ee-f923-4d9b-870d-35c7341b1c49
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted card le ring Krull Dim d0af2d24d2d7: P2 M Ground Theory Heights  Heights Field Numbers PFContracted card le ring Krull Dim d0af2d24d2d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted card le ring Krull Dim d0af2d24d2d7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted card le ring Krull Dim d0af2d24d2d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L134-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L134-L179

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_card_le_ringKrullDim_d0af2d24d2d7 [Fintype K] {Q : Ideal (MRing ι F)} [hQp : Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q) :
    (Fintype.card K : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«card_le_ringKrullDim» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_card_le_ringKrullDim_d0af2d24d2d7
