-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_norm_int_eq_norm_rat
-- name    : ReciprocityTheory.ChartRestriction.G.AI.norm_int_eq_norm_rat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:11.018927+00:00
-- url     : https://prove2.me/theorems/afa147ad-55e2-52ef-af69-8097024df645
-- title:
--   AI: norm int eq norm rat
-- statement:
--   The AI construction uses the norm int eq norm rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/CardQuotEqNatAbsNorm.lean#L34-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/CardQuotEqNatAbsNorm.lean#L34-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CardQuotEqNatAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module

theorem ReciprocityTheory.ChartRestriction.G.AI.norm_int_eq_norm_rat {K : Type*} [Field K] [NumberField K] (O : Subring K)
    [Module.Free ℤ O] [Module.Finite ℤ O] (h : Module.finrank ℤ O = Module.finrank ℚ K)
    (f : O) : ((Algebra.norm ℤ f : ℤ) : ℚ) = Algebra.norm ℚ (f : K) := by sorry
