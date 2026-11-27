-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_some_99ecb9fc8367
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_some_99ecb9fc8367
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:10:56.309239+00:00
-- url     : https://prove2.me/theorems/fe8f8e1a-44ad-5bfa-bf0c-3b8d95bd30d1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg some 99ecb9fc8367: P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg some 99ecb9fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg some 99ecb9fc8367 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg some 99ecb9fc8367 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L82-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
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
open GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
variable {F : Type u} [Field F] {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_some_99ecb9fc8367 (c : K → ℤ) :
    pullDeg (Function.Embedding.some : K ↪ Option K) c =
      IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := Unit) c ∘ blockEquiv K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«AddBlockFunctionField».«pullDeg_some» := P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_some_99ecb9fc8367
