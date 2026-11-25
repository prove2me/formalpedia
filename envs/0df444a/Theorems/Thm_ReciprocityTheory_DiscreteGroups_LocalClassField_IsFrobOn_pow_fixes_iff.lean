-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_pow_fixes_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.pow_fixes_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:03.950381+00:00
-- url     : https://prove2.me/theorems/aded7d63-4b4f-58be-a14f-ad6db20784c9
-- title:
--   Is Frob On: pow fixes iff
-- statement:
--   The Is Frob On construction uses the pow fixes iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L136-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L136-L160

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.pow_fixes_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (i : ℕ) : (∀ x ∈ Kn p K n, (φ ^ i) x = x) ↔ n ∣ i := by sorry
