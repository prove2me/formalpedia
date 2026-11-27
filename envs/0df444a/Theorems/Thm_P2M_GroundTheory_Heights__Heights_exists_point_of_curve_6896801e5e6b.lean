-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_point_of_curve_6896801e5e6b
-- name    : P2M_GroundTheory_Heights__Heights_exists_point_of_curve_6896801e5e6b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:43.135827+00:00
-- url     : https://prove2.me/theorems/1dd53e65-b113-4a83-ab79-dcc3c09cad0f
-- title:
--   P2 M Ground Theory Heights  Heights exists point of curve 6896801e5e6b: P2 M Ground Theory Heights  Heights exists point of curve 6896801e5e6b
-- statement:
--   The P2 M Ground Theory Heights  Heights exists point of curve 6896801e5e6b construction uses the P2 M Ground Theory Heights  Heights exists point of curve 6896801e5e6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L536-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L536-L540

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

theorem P2M_GroundTheory_Heights__Heights_exists_point_of_curve_6896801e5e6b (hC : CurveIsOrbit.Statement) (P : ArithVariety n)
    {W : Ideal (MvPolynomial (Coord n) ℤ)} (hW : Geo.IsArithVar (ι := blockIdx n) W 1)
    (hPW : P.ideal ≤ W) : ∃ x ∈ P.points (AlgebraicClosure ℚ), W = orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_point_of_curve» := P2M_GroundTheory_Heights__Heights_exists_point_of_curve_6896801e5e6b
