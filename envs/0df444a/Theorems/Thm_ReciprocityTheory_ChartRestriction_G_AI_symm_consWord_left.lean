-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_consWord_left
-- name    : ReciprocityTheory.ChartRestriction.G.AI.symm_consWord_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:08.681311+00:00
-- url     : https://prove2.me/theorems/df8d47ec-faf6-5574-bd03-aa2c5dd8c7f7
-- title:
--   AI: symm cons Word left
-- statement:
--   The AI construction uses the symm cons Word left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L44-L52

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

theorem ReciprocityTheory.ChartRestriction.G.AI.symm_consWord_left {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by sorry
