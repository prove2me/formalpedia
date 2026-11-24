-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_support_coker
-- name    : ReciprocityTheory.ChartRestriction.G.AI.support_coker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:12.446403+00:00
-- url     : https://prove2.me/theorems/f2604a63-4b20-4a28-8014-8c2c391da060
-- title:
--   AI: support coker
-- statement:
--   The AI construction uses the support coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L72-L75

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

theorem ReciprocityTheory.ChartRestriction.G.AI.support_coker (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] (x : A) :
    support A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) = support A N ∩ zeroLocus {x} := by sorry
