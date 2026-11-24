-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_mk_c349b29b8888
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_mk_c349b29b8888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:45.317714+00:00
-- url     : https://prove2.me/theorems/aa1258c5-0821-49d5-b4c3-4cbd9d499bd4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map mk c349b29b8888: P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map mk c349b29b8888
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map mk c349b29b8888 construction uses the P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map mk c349b29b8888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L38-L42

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_mk_c349b29b8888 (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«contractFracMap_mk» := P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_mk_c349b29b8888
