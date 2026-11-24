-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:14.572065+00:00
-- url     : https://prove2.me/theorems/1dae8b08-d455-42a8-8f2f-5719d3fea13d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rename split Var block Incl inl 10b826c66fda: P2 M Ground Theory Heights  Heights Field Numbers rename split Var block Incl inl 10b826c66fda
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rename split Var block Incl inl 10b826c66fda construction uses the P2 M Ground Theory Heights  Heights Field Numbers rename split Var block Incl inl 10b826c66fda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L44-L49

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Σ k, ι' (j k)) R) :
    rename (splitVar j ι')
        (rename (blockIncl (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitCoord j ι')) f) =
      rename (blockIncl j ι') f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«rename_splitVar_blockIncl_inl» := P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda
