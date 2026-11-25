-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_units_to_invariants_prime_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.units_to_invariants_prime_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:10.320368+00:00
-- url     : https://prove2.me/theorems/795b6048-53fa-4d8a-8f3f-cb586460b976
-- title:
--   Kummer: units to invariants prime injective
-- statement:
--   The Kummer construction uses the units to invariants prime injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L62-L66

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.units_to_invariants_prime_injective : Function.Injective (unitsToInvariants' p K) := by sorry
