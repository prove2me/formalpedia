-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_euler_finLength
-- name    : ReciprocityTheory.ChartRestriction.G.AI.euler_finLength
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:44.088852+00:00
-- url     : https://prove2.me/theorems/b2625af6-61ee-5e5b-884c-5d3fb742cee7
-- title:
--   AI: euler fin Length
-- statement:
--   The AI construction uses the euler fin Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L190-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L190-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
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

theorem ReciprocityTheory.ChartRestriction.G.AI.euler_finLength {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : length A N ≠ ⊤) (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (LinearMap.ker (LinearMap.lsmul A N x)) := by sorry
