-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_swap_nat
-- name    : ReciprocityTheory.ChartRestriction.G.AI.symm_swap_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:07.957978+00:00
-- url     : https://prove2.me/theorems/b82285e7-d542-4e65-bace-4c3e7de9cf7f
-- title:
--   AI: symm swap nat
-- statement:
--   The AI construction uses the symm swap nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L5-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI

theorem ReciprocityTheory.ChartRestriction.G.AI.symm_swap_nat {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (f : ℕ → V) (a b : ℕ)
    (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by sorry
