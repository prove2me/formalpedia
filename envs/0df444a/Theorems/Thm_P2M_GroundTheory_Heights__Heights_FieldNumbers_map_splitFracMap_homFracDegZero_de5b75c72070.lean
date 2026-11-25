-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:41.802858+00:00
-- url     : https://prove2.me/theorems/443fd228-9b6b-4304-87ef-55c61d59157a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers map split Frac Map hom Frac Deg Zero de5b75c72070: P2 M Ground Theory Heights  Heights Field Numbers map split Frac Map hom Frac Deg Zero de5b75c72070
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers map split Frac Map hom Frac Deg Zero de5b75c72070 construction uses the P2 M Ground Theory Heights  Heights Field Numbers map split Frac Map hom Frac Deg Zero de5b75c72070 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L81-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSplitRelDeg.lean#L81-L108

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070 [DecidableEq K] [DecidableEq K'] :
    (homFracDegZero (splitPrime j P')).map (splitFracMap j P') = homFracDegZero P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«map_splitFracMap_homFracDegZero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070
