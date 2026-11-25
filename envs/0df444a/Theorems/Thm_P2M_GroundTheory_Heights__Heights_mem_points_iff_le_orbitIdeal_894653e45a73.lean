-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73
-- name    : P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:00.904998+00:00
-- url     : https://prove2.me/theorems/99c0535e-b747-55e8-bad4-d37bc5697379
-- title:
--   P2 M Ground Theory Heights  Heights mem points iff le orbit Ideal 894653e45a73: P2 M Ground Theory Heights  Heights mem points iff le orbit Ideal 894653e45a73
-- statement:
--   The P2 M Ground Theory Heights  Heights mem points iff le orbit Ideal 894653e45a73 construction uses the P2 M Ground Theory Heights  Heights mem points iff le orbit Ideal 894653e45a73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L118-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73 (P : ArithVariety n) (x : Cone n (AlgebraicClosure ℚ)) :
    x ∈ P.points (AlgebraicClosure ℚ) ↔ BlockNonzero x ∧ P.ideal ≤ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_points_iff_le_orbitIdeal» := P2M_GroundTheory_Heights__Heights_mem_points_iff_le_orbitIdeal_894653e45a73
