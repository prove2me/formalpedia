-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_coeff_odd
-- name    : ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_coeff_odd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:19.651599+00:00
-- url     : https://prove2.me/theorems/0cd7a09d-c3b9-58a9-9fc8-bb57a575b43f
-- title:
--   AI: tsg Poly coeff odd
-- statement:
--   The AI construction uses the tsg Poly coeff odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/TsgPolyVolPolyCoeffEven.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/TsgPolyVolPolyCoeffEven.lean#L79-L81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Polynomial

theorem ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_coeff_odd (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) :
    (tsgPoly D κ P).coeff (2 * k + 1) = 0 := by sorry
