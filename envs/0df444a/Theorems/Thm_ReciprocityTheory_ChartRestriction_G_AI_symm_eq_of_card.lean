-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_eq_of_card
-- name    : ReciprocityTheory.ChartRestriction.G.AI.symm_eq_of_card
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:09.141208+00:00
-- url     : https://prove2.me/theorems/7a6f3471-27d2-4589-9592-9b65ce273d44
-- title:
--   AI: symm eq of card
-- statement:
--   The AI construction uses the symm eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/SymExp.lean#L5-L12

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

theorem ReciprocityTheory.ChartRestriction.G.AI.symm_eq_of_card {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (v w : Fin n → V)
    (h : ∀ x : V, (Finset.univ.filter fun i => v i = x).card = (Finset.univ.filter fun i => w i = x).card) :
    I v = I w := by sorry
