-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:45.880963+00:00
-- url     : https://prove2.me/theorems/8121cf38-d98f-4132-909f-26f165981ad4
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists number Field coords 38ed536ee690: P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists number Field coords 38ed536ee690
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists number Field coords 38ed536ee690 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists number Field coords 38ed536ee690 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L273-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L273-L300

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690 {T : Type} [Fintype T] (W : Ideal (MRing (fun _ : Unit => T)))
    (hW : IsArithVar W 1) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : (Σ _ : Unit, T) → L) (t0 : T),
      z ⟨(), t0⟩ = 1 ∧ mCoordIdeal z = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«exists_numberField_coords» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690
