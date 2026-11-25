-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_piecewise_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.symm_piecewise_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:11.192087+00:00
-- url     : https://prove2.me/theorems/7c6504ef-29ad-5539-b827-58dfd9766604
-- title:
--   AI: symm piecewise eq
-- statement:
--   The AI construction uses the symm piecewise eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L14-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI

theorem ReciprocityTheory.ChartRestriction.G.AI.symm_piecewise_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by sorry
