-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval_one_mConeMap_84e96b2abaec
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval_one_mConeMap_84e96b2abaec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:37.593581+00:00
-- url     : https://prove2.me/theorems/257f4e45-edab-42d7-b922-ec86b9f92467
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt eval one m Cone Map 84e96b2abaec: P2 M Ground Theory Heights  Heights Dual Curve Point Alt eval one m Cone Map 84e96b2abaec
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt eval one m Cone Map 84e96b2abaec construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt eval one m Cone Map 84e96b2abaec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L24-L29

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval_one_mConeMap_84e96b2abaec {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = eval₂ (Int.castRingHom Ω) y f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«eval_one_mConeMap» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval_one_mConeMap_84e96b2abaec
