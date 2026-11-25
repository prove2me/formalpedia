-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:47.788609+00:00
-- url     : https://prove2.me/theorems/38ea9329-ee3e-458a-93bc-9675808f7ecf
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval eq zero of mem 3ac1f31f332f: P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval eq zero of mem 3ac1f31f332f
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval eq zero of mem 3ac1f31f332f construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval eq zero of mem 3ac1f31f332f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L38-L40

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f {Ω : Type} [Field Ω] {z : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal z) : eval₂ (Int.castRingHom Ω) z f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«aeval_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
