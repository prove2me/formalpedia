-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_contDiffAt_log_metric_a11df366d392
-- name    : P2M_GroundTheory_Heights__Heights_Inter_contDiffAt_log_metric_a11df366d392
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:59.407837+00:00
-- url     : https://prove2.me/theorems/7fcc9e54-7a7b-4251-9a86-951b0fccc107
-- title:
--   P2 M Ground Theory Heights  Heights Inter cont Diff At log metric a11df366d392: P2 M Ground Theory Heights  Heights Inter cont Diff At log metric a11df366d392
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cont Diff At log metric a11df366d392 construction uses the P2 M Ground Theory Heights  Heights Inter cont Diff At log metric a11df366d392 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L25-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_contDiffAt_log_metric_a11df366d392 {D : ℕ} {A : HermLine ι} (hA : IsSmoothHerm A)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«contDiffAt_log_metric» := P2M_GroundTheory_Heights__Heights_Inter_contDiffAt_log_metric_a11df366d392
