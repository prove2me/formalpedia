-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:52.746815+00:00
-- url     : https://prove2.me/theorems/be0367e7-425b-406b-842e-19da3197b66d
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line transcendental div d53045909a4d: P2 M Ground Theory Heights  Heights Lower Bound Free Line transcendental div d53045909a4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line transcendental div d53045909a4d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line transcendental div d53045909a4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L21-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean#L21-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d {i j : Fin 2} (hij : i ≠ j) : Transcendental ℚ (xL i / xL j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«transcendental_div» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d
