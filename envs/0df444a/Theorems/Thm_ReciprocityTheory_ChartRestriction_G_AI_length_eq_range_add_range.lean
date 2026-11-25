-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_range_add_range
-- name    : ReciprocityTheory.ChartRestriction.G.AI.length_eq_range_add_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:44.260023+00:00
-- url     : https://prove2.me/theorems/d07a64ab-3d35-5843-a28e-39da985330d1
-- title:
--   AI: length eq range add range
-- statement:
--   The AI construction uses the length eq range add range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthEqRangeAddRange.lean#L19-L23

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

theorem ReciprocityTheory.ChartRestriction.G.AI.length_eq_range_add_range {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ψ : L →ₗ[A] M} {φ : M →ₗ[A] N} (h : Function.Exact ψ φ) :
    length A M = length A (LinearMap.range ψ) + length A (LinearMap.range φ) := by sorry
