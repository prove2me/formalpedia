-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_volPoly_coeff_even
-- name    : ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_volPoly_coeff_even
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:35.567862+00:00
-- url     : https://prove2.me/theorems/a98b9ba2-c309-4492-9975-991fc29ab12a
-- title:
--   AI: tsg Poly vol Poly coeff even
-- statement:
--   The AI construction uses the tsg Poly vol Poly coeff even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/TsgPolyVolPolyCoeffEven.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/TsgPolyVolPolyCoeffEven.lean#L55-L77

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

theorem ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_volPoly_coeff_even (D : ℕ) (J κ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (tsgPoly D κ (volPoly D J)).coeff (2 * k) =
      -(2 * ((D + 1).choose (2 * k) : ℝ) * (κ k * J (2 * k - 1))) := by sorry
