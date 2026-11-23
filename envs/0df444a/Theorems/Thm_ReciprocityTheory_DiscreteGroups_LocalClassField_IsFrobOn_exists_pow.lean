-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_exists_pow
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.exists_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:32.328687+00:00
-- url     : https://prove2.me/theorems/e859d585-d372-421c-a9ca-d57fbd3ef2d1
-- title:
--   Is Frob On: exists pow
-- statement:
--   The Is Frob On construction uses the exists pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L127-L134

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.exists_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (σ : GK p K) : ∃ i < n, ∀ x ∈ Kn p K n, σ x = (φ ^ i) x := by sorry
