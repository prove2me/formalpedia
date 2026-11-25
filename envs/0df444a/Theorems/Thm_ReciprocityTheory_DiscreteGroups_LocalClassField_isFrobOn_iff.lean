-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isFrobOn_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:41.8457+00:00
-- url     : https://prove2.me/theorems/75419a10-8364-42a7-9973-d480e9ff5ae5
-- title:
--   Local Class Field: is Frob On iff
-- statement:
--   The Local Class Field construction uses the is Frob On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L51-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L51-L77

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isFrobOn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (φ : GK p K) :
    IsFrobOn p K n φ ↔ ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K := by sorry
