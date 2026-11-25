-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:04.036943+00:00
-- url     : https://prove2.me/theorems/330fa540-13ff-4236-9302-7d0529aad630
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists eval eq 080797a46129: P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists eval eq 080797a46129
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists eval eq 080797a46129 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists eval eq 080797a46129 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L195-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L195-L208

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129 (b : Module.Basis T ℤ (dualLattice F)) (t0 : T) (w : Fin i → K) :
    ∃ g : MvPolynomial (Σ _ : Unit, T) ℚ,
      eval₂ (Rat.castHom _) (fun p => dualLatticeCoord b p / dualLatticeCoord b ⟨(), t0⟩) g =
        linVal w / dualLatticeCoord b ⟨(), t0⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«exists_eval_eq» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129
