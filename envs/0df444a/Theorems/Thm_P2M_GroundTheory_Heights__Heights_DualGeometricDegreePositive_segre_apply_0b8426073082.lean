-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:43.626734+00:00
-- url     : https://prove2.me/theorems/cf2cd210-9e06-5185-9dfb-69dd50fcd24c
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive segre apply 0b8426073082: P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive segre apply 0b8426073082
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive segre apply 0b8426073082 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Positive segre apply 0b8426073082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegPos.lean#L34-L36

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

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082 (z : (Σ _ : Unit, T) → ℂ) (s : (k : Unit) → dualBlocks T k) :
    segre (ι := dualBlocks T) z s = z ⟨(), s ()⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreePositive».«segre_apply» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082
