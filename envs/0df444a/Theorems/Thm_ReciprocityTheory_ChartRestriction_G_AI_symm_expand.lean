-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_expand
-- name    : ReciprocityTheory.ChartRestriction.G.AI.symm_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:15.216522+00:00
-- url     : https://prove2.me/theorems/bfb12637-b713-5edf-9d36-e9ec19de7263
-- title:
--   AI: symm expand
-- statement:
--   The AI construction uses the symm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L67-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L67-L90

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

theorem ReciprocityTheory.ChartRestriction.G.AI.symm_expand {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by sorry
