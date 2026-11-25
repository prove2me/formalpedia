-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:31.244+00:00
-- url     : https://prove2.me/theorems/d95349f9-936b-4dad-818a-1f2832f62f29
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists combo 326d57212312: P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists combo 326d57212312
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists combo 326d57212312 construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt exists combo 326d57212312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L174-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L174-L193

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312 (b : Module.Basis T ℤ (dualLattice F)) (w : Fin i → K) :
    ∃ (D : ℤ) (c : T → ℤ), D ≠ 0 ∧
      (D : ProjField K i) * linVal w = ∑ t, (c t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«exists_combo» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312
