-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.red_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:30.54912+00:00
-- url     : https://prove2.me/theorems/f5708588-2673-4108-8578-8177d07d4561
-- title:
--   Unramified Extensions: red pow
-- statement:
--   The Unramified Extensions construction uses the red pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L19-L21

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.red_pow {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (k : ℕ) : red (x ^ k) = red x ^ k := by sorry
