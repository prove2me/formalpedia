-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:39.890026+00:00
-- url     : https://prove2.me/theorems/be90b9ab-7eac-4cb9-97e9-a8fa27fc08c9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers split Frac Map contract Frac Map inl mk c258701bd505: P2 M Ground Theory Heights  Heights Field Numbers split Frac Map contract Frac Map inl mk c25870
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers split Frac Map contract Frac Map inl mk c258701bd505 construction uses the P2 M Ground Theory Heights  Heights Field Numbers split Frac Map contract Frac Map inl mk c258701bd505 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L68-L79

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505 (f : MRing (fun k => ι' (j k)) F) :
    splitFracMap j P' (contractFracMap (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P') (algebraMap _ _
          (Ideal.Quotient.mk (contractPrime Function.Embedding.inl (splitPrime j P')) f))) =
      contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«splitFracMap_contractFracMap_inl_mk» := P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505
