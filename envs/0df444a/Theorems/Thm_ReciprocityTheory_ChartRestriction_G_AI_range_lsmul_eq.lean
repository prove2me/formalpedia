-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_range_lsmul_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.range_lsmul_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:06.109145+00:00
-- url     : https://prove2.me/theorems/a164b273-c89e-4edd-ac5c-0c8c4247f6bf
-- title:
--   AI: range lsmul eq
-- statement:
--   The AI construction uses the range lsmul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L66-L70

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

theorem ReciprocityTheory.ChartRestriction.G.AI.range_lsmul_eq (N : Type v) [AddCommGroup N] [Module A N] (x : A) :
    LinearMap.range (LinearMap.lsmul A N x) = x • (⊤ : Submodule A N) := by sorry
