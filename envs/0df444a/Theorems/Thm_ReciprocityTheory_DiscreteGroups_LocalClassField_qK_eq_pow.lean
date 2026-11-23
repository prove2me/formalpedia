-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_eq_pow
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:16.449543+00:00
-- url     : https://prove2.me/theorems/7ebf129a-8a96-4e32-9a13-7198480e47a1
-- title:
--   Local Class Field: q K eq pow
-- statement:
--   The Local Class Field construction uses the q K eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L27-L28

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_eq_pow

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow (hK : FiniteDimensional ℚ_[p] K) : ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f := by sorry
