-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_euler_ses
-- name    : ReciprocityTheory.ChartRestriction.G.AI.euler_ses
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:57.762683+00:00
-- url     : https://prove2.me/theorems/d1624941-976d-4965-8c73-dd8bab57f8a6
-- title:
--   AI: euler ses
-- statement:
--   The AI construction uses the euler ses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L56-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L56-L188

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

theorem ReciprocityTheory.ChartRestriction.G.AI.euler_ses {A : Type*} [CommRing A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (x : A) :
    length A (LinearMap.ker (LinearMap.lsmul A M' x)) + length A (LinearMap.ker (LinearMap.lsmul A M'' x)) +
        length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)) +
        length A (M'' ⧸ LinearMap.range (LinearMap.lsmul A M'' x)) := by sorry
