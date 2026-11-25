-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_cons_cons_word
-- name    : ReciprocityTheory.ChartRestriction.G.AI.cons_cons_word
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:50.936881+00:00
-- url     : https://prove2.me/theorems/16e34e23-e774-509b-97e1-96ed6f3036b4
-- title:
--   AI: cons cons word
-- statement:
--   The AI construction uses the cons cons word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/APrime.lean#L33-L42

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

theorem ReciprocityTheory.ChartRestriction.G.AI.cons_cons_word {VW : Type*} (D k i : ℕ) (hk : 1 ≤ k) (x x₁ x₂ a : VW) :
    (Fin.cons x (Fin.cons x (word D k i x₁ x₂ a)) : Fin (D + 2) → VW) =
      fun j : Fin (D + 2) => consWord k i x x₁ x₂ a j := by sorry
