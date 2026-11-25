-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_card_QZ_torsion
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.card_QZ_torsion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:45.276925+00:00
-- url     : https://prove2.me/theorems/262f334d-15cf-42d7-92dc-122aa5f28cc8
-- title:
--   Local Class Field: card QZ torsion
-- statement:
--   The Local Class Field construction uses the card QZ torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L25-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L25-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.card_QZ_torsion (n : ℕ) (hn : 0 < n) : Nat.card {a : QZ // n • a = 0} = n := by sorry
