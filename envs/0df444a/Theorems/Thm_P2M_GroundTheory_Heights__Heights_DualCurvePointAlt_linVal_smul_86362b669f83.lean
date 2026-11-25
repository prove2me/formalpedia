-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_smul_86362b669f83
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_smul_86362b669f83
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:42.703879+00:00
-- url     : https://prove2.me/theorems/09399e2b-8974-4059-a8d1-1987e894ecda
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val smul 86362b669f83: P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val smul 86362b669f83
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val smul 86362b669f83 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val smul 86362b669f83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L161-L164

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_smul_86362b669f83 (a : K) (w : Fin i → K) : linVal (a • w) = constK K i a * linVal w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«linVal_smul» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_smul_86362b669f83
