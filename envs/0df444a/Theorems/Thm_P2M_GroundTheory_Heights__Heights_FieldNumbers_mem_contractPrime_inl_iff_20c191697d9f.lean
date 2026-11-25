-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:52.900612+00:00
-- url     : https://prove2.me/theorems/2a13e1d3-5c24-41ee-853d-dce9725037a3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mem contract Prime inl iff 20c191697d9f: P2 M Ground Theory Heights  Heights Field Numbers mem contract Prime inl iff 20c191697d9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mem contract Prime inl iff 20c191697d9f construction uses the P2 M Ground Theory Heights  Heights Field Numbers mem contract Prime inl iff 20c191697d9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L63-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
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
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
omit [P'.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f (g : MRing (fun k => ι' (j k)) F) :
    g ∈ contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P') ↔
      g ∈ contractPrime j P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mem_contractPrime_inl_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f
