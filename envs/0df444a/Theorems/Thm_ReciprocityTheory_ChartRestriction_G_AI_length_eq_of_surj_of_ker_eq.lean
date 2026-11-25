-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_of_surj_of_ker_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_eq_of_surj_of_ker_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:17.294138+00:00
-- url     : https://prove2.me/theorems/ddbf1429-99cd-583b-b3bf-9556f8f1af04
-- title:
--   AI: length eq of surj of ker eq
-- statement:
--   The AI construction uses the length eq of surj of ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L7-L11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
universe u

theorem ReciprocityTheory.ChartRestriction.G.AI.length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := by sorry
