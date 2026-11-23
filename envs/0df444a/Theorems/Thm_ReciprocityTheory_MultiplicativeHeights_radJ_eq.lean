-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.radJ_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:54.96329+00:00
-- url     : https://prove2.me/theorems/8c927751-f589-46be-aa4b-3f51434e456e
-- title:
--   Multiplicative Heights: rad J eq
-- statement:
--   The Multiplicative Heights construction uses the rad J eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L19-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology

theorem ReciprocityTheory.MultiplicativeHeights.radJ_eq (k : ℕ) : radJ k = Gamma (((k : ℝ) + 1) / 2) / 2 := by sorry
