-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e
-- name    : P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:26.835591+00:00
-- url     : https://prove2.me/theorems/eeb920f7-74c9-4e0b-b998-fb1dadb74631
-- title:
--   P2 M Ground Theory Heights  Heights Dual Curve Point Alt ker cone Map Q eq b779a2ea9f5e: P2 M Ground Theory Heights  Heights Dual Curve Point Alt ker cone Map Q eq b779a2ea9f5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Curve Point Alt ker cone Map Q eq b779a2ea9f5e construction uses the P2 M Ground Theory Heights  Heights Dual Curve Point Alt ker cone Map Q eq b779a2ea9f5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean#L78-L91

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

theorem P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) :
    RingHom.ker (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualCurvePointAlt».«ker_coneMapQ_eq» := P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e
