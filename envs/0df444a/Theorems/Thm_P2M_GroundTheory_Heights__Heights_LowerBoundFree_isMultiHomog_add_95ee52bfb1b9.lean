-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:45.279734+00:00
-- url     : https://prove2.me/theorems/c410f647-6195-4275-936d-1c24c92b6f4c
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog add 95ee52bfb1b9: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog add 95ee52bfb1b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog add 95ee52bfb1b9 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog add 95ee52bfb1b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L21-L27

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9 {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g + h) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_add» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
