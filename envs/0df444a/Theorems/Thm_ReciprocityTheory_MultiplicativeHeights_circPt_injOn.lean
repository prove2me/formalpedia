-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_circPt_injOn
-- name    : ReciprocityTheory.MultiplicativeHeights.circPt_injOn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:03.463956+00:00
-- url     : https://prove2.me/theorems/e80f291f-3682-4835-ab05-26867e50836d
-- title:
--   Multiplicative Heights: circ Pt inj On
-- statement:
--   The Multiplicative Heights construction uses the circ Pt inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L70-L82

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

theorem ReciprocityTheory.MultiplicativeHeights.circPt_injOn : Set.InjOn circPt (Set.Ioc (0 : ℝ) 1) := by sorry
