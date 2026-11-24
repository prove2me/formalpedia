-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_self_03d3c378e4e7
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_self_03d3c378e4e7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:35.122009+00:00
-- url     : https://prove2.me/theorems/6d4f83e2-607b-4658-b178-23e2ce007f00
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At one self 03d3c378e4e7: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At one self 03d3c378e4e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At one self 03d3c378e4e7 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At one self 03d3c378e4e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L99-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_self_03d3c378e4e7 (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y 1 z 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_one_self» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_self_03d3c378e4e7
