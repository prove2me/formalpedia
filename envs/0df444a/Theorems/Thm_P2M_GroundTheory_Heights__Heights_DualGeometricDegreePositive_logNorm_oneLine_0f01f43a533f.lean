-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_logNorm_oneLine_0f01f43a533f
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_logNorm_oneLine_0f01f43a533f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:17.918914+00:00
-- url     : https://prove2.me/theorems/76add0fa-f6bb-47b5-b6ba-44513a06e86f
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive log Norm one Line 0f01f43a533f: P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive log Norm one Line 0f01f43a533f
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive log Norm one Line 0f01f43a533f construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive log Norm one Line 0f01f43a533f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L29-L31

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
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_logNorm_oneLine_0f01f43a533f : logNorm (oneLine (T := T)) 1 = fun _ => (1 : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreePositive».«logNorm_oneLine» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_logNorm_oneLine_0f01f43a533f
