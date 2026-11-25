-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:44:29.852171+00:00
-- url     : https://prove2.me/theorems/8b6039da-c530-572d-a40f-e03f1971af9b
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval ratio eq zero of le 3480b1786d6e: P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval ratio eq zero of le 3480b1786d6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval ratio eq zero of le 3480b1786d6e construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt aeval ratio eq zero of le 3480b1786d6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L95-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L95-L132

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
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e {Ω L : Type} [Field Ω] [CharZero Ω] [Field L] [CharZero L]
    {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hyz : mCoordIdeal y ≤ mCoordIdeal z) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) (hzd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p => y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p => z p / z ⟨p.1, d p.1⟩) g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«aeval_ratio_eq_zero_of_le» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e
