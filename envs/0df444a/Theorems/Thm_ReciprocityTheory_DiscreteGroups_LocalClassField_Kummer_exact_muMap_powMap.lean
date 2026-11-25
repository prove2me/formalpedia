-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_exact_muMap_powMap
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.exact_muMap_powMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:22.361181+00:00
-- url     : https://prove2.me/theorems/19ca7cfc-e039-5c49-aee9-7cfaaa4c8dc6
-- title:
--   Kummer: exact mu Map pow Map
-- statement:
--   The Kummer construction uses the exact mu Map pow Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L142-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L142-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
open _root_.Neutral.B1
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
variable {p n}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.exact_muMap_powMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by sorry
