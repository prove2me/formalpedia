-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quot_prime_ne_top_iff
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_quot_prime_ne_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:59.73701+00:00
-- url     : https://prove2.me/theorems/6a585842-b658-42ec-907d-10ec02fb42af
-- title:
--   AI: length quot prime ne top iff
-- statement:
--   The AI construction uses the length quot prime ne top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L14-L35

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_quot_prime_ne_top_iff (q : Ideal A) [q.IsPrime] :
    length A (A ⧸ q) ≠ ⊤ ↔ q.IsMaximal := by sorry
