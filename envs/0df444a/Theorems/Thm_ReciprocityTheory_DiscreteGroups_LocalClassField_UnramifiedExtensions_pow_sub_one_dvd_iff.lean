-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_sub_one_dvd_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_sub_one_dvd_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:45.88209+00:00
-- url     : https://prove2.me/theorems/f7c02ba5-cc64-5a9b-8394-a6ff8f09bd98
-- title:
--   Unramified Extensions: pow sub one dvd iff
-- statement:
--   The Unramified Extensions construction uses the pow sub one dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L33-L45

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_sub_one_dvd_iff {q : ℕ} (hq : 1 < q) {n : ℕ} (i : ℕ) :
    q ^ n - 1 ∣ q ^ i - 1 ↔ n ∣ i := by sorry
