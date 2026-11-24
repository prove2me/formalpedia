-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_add
-- name    : ReciprocityTheory.ChartRestriction.G.AI.locLen_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:03.332985+00:00
-- url     : https://prove2.me/theorems/976ac7be-36c8-4d70-8120-f46c56f3e1a5
-- title:
--   AI: loc Len add
-- statement:
--   The AI construction uses the loc Len add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L86-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L86-L104

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

theorem ReciprocityTheory.ChartRestriction.G.AI.locLen_add {N₁ N₂ N₃ : Type v} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (p : PrimeSpectrum A) : locLen N₂ p = locLen N₁ p + locLen N₃ p := by sorry
