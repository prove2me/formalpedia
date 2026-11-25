-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_of_dvd
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.of_dvd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:52.473807+00:00
-- url     : https://prove2.me/theorems/874c60b5-a9bf-5dce-833d-e428c81a26c9
-- title:
--   Is Frob On: of dvd
-- statement:
--   The Is Frob On construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L162-L164

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
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.of_dvd (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) : IsFrobOn p K m φ := by sorry
