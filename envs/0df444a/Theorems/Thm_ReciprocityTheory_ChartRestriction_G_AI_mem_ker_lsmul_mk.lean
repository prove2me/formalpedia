-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_mem_ker_lsmul_mk
-- name    : ReciprocityTheory.ChartRestriction.G.AI.mem_ker_lsmul_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:36.014078+00:00
-- url     : https://prove2.me/theorems/cc84efa0-7494-4384-978c-b28f309c9c74
-- title:
--   AI: mem ker lsmul mk
-- statement:
--   The AI construction uses the mem ker lsmul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqOfSurjOfKerEq.lean#L13-L18

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

theorem ReciprocityTheory.ChartRestriction.G.AI.mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by sorry
