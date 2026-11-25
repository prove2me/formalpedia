-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_power_map_h0_unitsToInvariants
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.power_map_h0_unitsToInvariants
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:00:58.515481+00:00
-- url     : https://prove2.me/theorems/328c39eb-4440-45d7-bef7-cd176c52637d
-- title:
--   Kummer: power map h0 units To Invariants
-- statement:
--   The Kummer construction uses the power map h0 units To Invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L80-L85

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
open ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.power_map_h0_unitsToInvariants (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by sorry
