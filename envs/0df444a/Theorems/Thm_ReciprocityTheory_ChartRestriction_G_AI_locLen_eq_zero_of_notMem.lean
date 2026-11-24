-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_eq_zero_of_notMem
-- name    : ReciprocityTheory.ChartRestriction.G.AI.locLen_eq_zero_of_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:38.771789+00:00
-- url     : https://prove2.me/theorems/ebe73ea9-9ccd-483e-80f6-2b78e072a7b0
-- title:
--   AI: loc Len eq zero of not Mem
-- statement:
--   The AI construction uses the loc Len eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L106-L113

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
variable {A : Type u} [CommRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.locLen_eq_zero_of_notMem {N : Type v} [AddCommGroup N] [Module A N] (p : PrimeSpectrum A)
    (hp : p ∉ support A N) : locLen N p = 0 := by sorry
