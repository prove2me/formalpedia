-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_circPt_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.circPt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:52.884799+00:00
-- url     : https://prove2.me/theorems/a6d94edd-bc61-4578-90f4-aab4d6b157ae
-- title:
--   Multiplicative Heights: circ Pt eq
-- statement:
--   The Multiplicative Heights construction uses the circ Pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L11-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
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
open MeasureTheory Polynomial Real

theorem ReciprocityTheory.MultiplicativeHeights.circPt_eq (t : ℝ) : circPt t = circleMap 0 1 (2 * π * t) := by sorry
