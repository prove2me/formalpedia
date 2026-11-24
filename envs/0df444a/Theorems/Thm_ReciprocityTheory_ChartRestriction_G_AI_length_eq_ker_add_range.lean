-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_ker_add_range
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_eq_ker_add_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:03.318572+00:00
-- url     : https://prove2.me/theorems/3b209a95-f35a-410d-941a-f5ca388e2f77
-- title:
--   AI: length eq ker add range
-- statement:
--   The AI construction uses the length eq ker add range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L7-L12

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_eq_ker_add_range {A : Type*} [Ring A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    length A M = length A (LinearMap.ker φ) + length A (LinearMap.range φ) := by sorry
