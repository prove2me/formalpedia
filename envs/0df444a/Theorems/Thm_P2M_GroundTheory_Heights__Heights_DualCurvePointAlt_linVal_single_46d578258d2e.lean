-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_single_46d578258d2e
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_single_46d578258d2e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:44.816313+00:00
-- url     : https://prove2.me/theorems/37db8bd3-69a0-4bf8-824a-0d1d96e8dbe2
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val single 46d578258d2e: P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val single 46d578258d2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val single 46d578258d2e construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val single 46d578258d2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L166-L169

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
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_single_46d578258d2e (j : Fin i) :
    linVal (Pi.single j (1 : K)) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«linVal_single» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_single_46d578258d2e
