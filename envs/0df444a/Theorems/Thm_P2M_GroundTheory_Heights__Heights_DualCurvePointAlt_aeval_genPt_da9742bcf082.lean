-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:21.997478+00:00
-- url     : https://prove2.me/theorems/74884ed5-a24a-55e4-90b9-44d0c24bd64f
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval gen Pt da9742bcf082: P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval gen Pt da9742bcf082
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval gen Pt da9742bcf082 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval gen Pt da9742bcf082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L42-L48

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082 (W : Ideal (MRing ι)) (f : MRing ι) :
    eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.Inter.genPt W) f =
      algebraMap (MRing ι ⧸ W) (IndefiniteRowSideFullHecke.Inter.FnField W) (Ideal.Quotient.mk W f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«aeval_genPt» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_genPt_da9742bcf082
