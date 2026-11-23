-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:41.972468+00:00
-- url     : https://prove2.me/theorems/6f426358-d2c4-4cb2-a200-3d72755f0ac1
-- title:
--   Unramified Extensions: norm eq one of pow
-- statement:
--   The Unramified Extensions construction uses the norm eq one of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L135-L136

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow {m : ℕ} (hm : m ≠ 0) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : ‖ζ‖ = 1 := by sorry
