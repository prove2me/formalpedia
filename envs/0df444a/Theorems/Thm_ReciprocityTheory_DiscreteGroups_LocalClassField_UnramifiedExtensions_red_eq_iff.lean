-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.red_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:29.903847+00:00
-- url     : https://prove2.me/theorems/ba4223d2-b4d9-4684-a512-830bbb4aa8a1
-- title:
--   Unramified Extensions: red eq iff
-- statement:
--   The Unramified Extensions construction uses the red eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L16-L17

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
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
variable {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.red_eq_iff {x y : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : red x = red y ↔ ‖x - y‖ < 1 := by sorry
