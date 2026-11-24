-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ne_top_iff_support
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_iff_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:41.378878+00:00
-- url     : https://prove2.me/theorems/3d8c31ec-9442-4bae-8539-6e2c0552decc
-- title:
--   AI: length ne top iff support
-- statement:
--   The AI construction uses the length ne top iff support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L37-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_iff_support (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] :
    length A N ≠ ⊤ ↔ ∀ p ∈ support A N, p.asIdeal.IsMaximal := by sorry
