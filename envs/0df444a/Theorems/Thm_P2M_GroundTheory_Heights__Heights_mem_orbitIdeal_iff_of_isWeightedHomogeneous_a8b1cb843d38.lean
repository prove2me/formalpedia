-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38
-- name    : P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:39.449072+00:00
-- url     : https://prove2.me/theorems/55c2c066-7fd2-59e3-9554-c9f106f74360
-- title:
--   P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Weighted Homogeneous a8b1cb843d38: P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Weighted Homogeneous a8b1cb843d38
-- statement:
--   The P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Weighted Homogeneous a8b1cb843d38 construction uses the P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Weighted Homogeneous a8b1cb843d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L113-L116

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

theorem P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38 (x : Cone n (AlgebraicClosure ℚ))
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ orbitIdeal x ↔ evalCone x g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_orbitIdeal_iff_of_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isWeightedHomogeneous_a8b1cb843d38
