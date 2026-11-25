-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ul_card_residue_eq
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.ul_card_residue_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:40.437731+00:00
-- url     : https://prove2.me/theorems/95ee1da9-7cc4-4acb-9e27-1f6be3c50023
-- title:
--   Global Class Field: ul card residue eq
-- statement:
--   The Global Class Field construction uses the ul card residue eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/LocPowB.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/LocPowB.lean#L10-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open NumberField IsDedekindDomain

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.ul_card_residue_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) =
      Ideal.absNorm v.asIdeal := by sorry
