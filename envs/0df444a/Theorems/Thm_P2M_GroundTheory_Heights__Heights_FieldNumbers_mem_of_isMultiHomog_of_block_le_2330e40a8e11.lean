-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_isMultiHomog_of_block_le_2330e40a8e11
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_isMultiHomog_of_block_le_2330e40a8e11
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:19.565109+00:00
-- url     : https://prove2.me/theorems/e7b5f296-30dc-42fb-8f51-e7e4b8db30f5
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mem of is Multi Homog of block le 2330e40a8e11: P2 M Ground Theory Heights  Heights Field Numbers mem of is Multi Homog of block le 2330e40a8e11
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mem of is Multi Homog of block le 2330e40a8e11 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mem of is Multi Homog of block le 2330e40a8e11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbIrrelevantZero.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbIrrelevantZero.lean#L21-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbIrrelevantZero
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_isMultiHomog_of_block_le_2330e40a8e11 {I : Ideal (MRing ι F)} {k : K}
    (hk : ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I) {b : K → ℕ} (hb : 1 ≤ b k)
    {f : MRing ι F} (hf : IsWeightedHomogeneous (blockWeight ι) f b) : f ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mem_of_isMultiHomog_of_block_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_isMultiHomog_of_block_le_2330e40a8e11
