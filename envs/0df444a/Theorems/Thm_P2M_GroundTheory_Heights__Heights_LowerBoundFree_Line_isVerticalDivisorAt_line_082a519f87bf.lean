-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isVerticalDivisorAt_line_082a519f87bf
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isVerticalDivisorAt_line_082a519f87bf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:14.05968+00:00
-- url     : https://prove2.me/theorems/d3f8766e-b599-4fea-80a8-4a6486d58054
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line is Vertical Divisor At line 082a519f87bf: P2 M Ground Theory Heights  Heights Lower Bound Free Line is Vertical Divisor At line 082a519f87bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line is Vertical Divisor At line 082a519f87bf construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line is Vertical Divisor At line 082a519f87bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/Example.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/Example.lean#L201-L203

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isVerticalDivisorAt_line_082a519f87bf {p : ℕ} (hp : p ≠ 0) :
    IsVerticalDivisorAt (mCoordIdeal yLine) p 0 (C (p : ℤ)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«isVerticalDivisorAt_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isVerticalDivisorAt_line_082a519f87bf
