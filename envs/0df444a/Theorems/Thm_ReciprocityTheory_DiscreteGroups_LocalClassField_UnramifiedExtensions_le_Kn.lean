-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.le_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:10.196041+00:00
-- url     : https://prove2.me/theorems/8bc92fe8-6991-4695-a897-9fc1381ac650
-- title:
--   Unramified Extensions: le Kn
-- statement:
--   The Unramified Extensions construction uses the le Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L102-L102

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (K)

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.le_Kn (n : ℕ) : K ≤ Kn p K n := by sorry
