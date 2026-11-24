-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:31.10023+00:00
-- url     : https://prove2.me/theorems/8ae7cffe-0b0d-4877-86a1-d9d3f9574fa8
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog one 0a1e8350c35d: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog one 0a1e8350c35d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog one 0a1e8350c35d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog one 0a1e8350c35d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L38-L39

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d : IsMultiHomog (1 : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_one» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_one_0a1e8350c35d
