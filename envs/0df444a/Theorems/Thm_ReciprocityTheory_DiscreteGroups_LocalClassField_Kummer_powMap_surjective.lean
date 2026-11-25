-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_powMap_surjective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.powMap_surjective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:46.18214+00:00
-- url     : https://prove2.me/theorems/734add5a-d767-592d-9abc-91adfc673852
-- title:
--   Kummer: pow Map surjective
-- statement:
--   The Kummer construction uses the pow Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L131-L140

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.powMap_surjective : Function.Surjective (powMap p n) := by sorry
