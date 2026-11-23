-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_pos
-- name    : ReciprocityTheory.MultiplicativeHeights.radJ_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:16.103808+00:00
-- url     : https://prove2.me/theorems/4acf3b5a-4654-4adf-a932-010ac5894e11
-- title:
--   Multiplicative Heights: rad J pos
-- statement:
--   The Multiplicative Heights construction uses the rad J pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean#L25-L27

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

theorem ReciprocityTheory.MultiplicativeHeights.radJ_pos (k : ℕ) : 0 < radJ k := by sorry
