-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:15.721293+00:00
-- url     : https://prove2.me/theorems/dae448e2-2e56-4783-84e1-2bc488a97e0c
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive is Good Proj 9122b7c98d31: P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive is Good Proj 9122b7c98d31
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive is Good Proj 9122b7c98d31 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive is Good Proj 9122b7c98d31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L38-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos
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
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31 (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreePositive».«isGoodProj» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31
