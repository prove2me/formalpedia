-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:08.14525+00:00
-- url     : https://prove2.me/theorems/1384bf93-7660-46d7-9add-009751617b54
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val eq c5bae4ee8eec: P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val eq c5bae4ee8eec
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val eq c5bae4ee8eec construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt lin Val eq c5bae4ee8eec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L157-L159

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec (w : Fin i → K) :
    linVal w = ∑ j, constK K i (w j) * algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«linVal_eq» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec
