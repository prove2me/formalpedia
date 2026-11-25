-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:09.964658+00:00
-- url     : https://prove2.me/theorems/25880293-8af4-4deb-9b79-6a65072cf093
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Cone Map eq eval  a0f62726315a: P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Cone Map eq eval  a0f62726315a
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Cone Map eq eval  a0f62726315a construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt m Cone Map eq eval  a0f62726315a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L31-L36

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    mConeMap y f = eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«mConeMap_eq_eval₂» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_mConeMap_eq_eval__a0f62726315a
