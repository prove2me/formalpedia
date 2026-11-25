-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:54.695558+00:00
-- url     : https://prove2.me/theorems/36111c5f-c692-4c3b-9ae3-aed3d1d63c36
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists point d98209b0a482: P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists point d98209b0a482
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists point d98209b0a482 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists point d98209b0a482 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L210-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L210-L269

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482 (b : Module.Basis T ℤ (dualLattice F)) {L : Type} [Field L] [CharZero L]
    (z : (Σ _ : Unit, T) → L) (t0 : T) (hz : z ⟨(), t0⟩ = 1) (hle : dualIdeal b ≤ mCoordIdeal z) :
    ∃ (_ : Algebra K L) (v : Fin i → L), v ≠ 0 ∧ dualPointCoord b v = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«exists_point» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482
