-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_muRep_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.muRep_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:40.653851+00:00
-- url     : https://prove2.me/theorems/59897bd3-327e-56d4-a1cb-d892ac658763
-- title:
--   Kummer: mu Rep apply
-- statement:
--   The Kummer construction uses the mu Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L93-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L93-L93

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.muRep_apply (g : GK p K) (x : ZMod n) : muRep p K n g x = ((cycK p K n g : (ZMod n)ˣ) : ZMod n) * x := by sorry
