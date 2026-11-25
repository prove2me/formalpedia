-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:37.978274+00:00
-- url     : https://prove2.me/theorems/22413229-099c-40bd-92d0-a9fc000e7124
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Coord Ideal gen Pt 4a2d546de20c: P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Coord Ideal gen Pt 4a2d546de20c
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Coord Ideal gen Pt 4a2d546de20c construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Coord Ideal gen Pt 4a2d546de20c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L50-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L50-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (IndefiniteRowSideFullHecke.Inter.genPt W) = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«mCoordIdeal_genPt» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mCoordIdeal_genPt_4a2d546de20c
