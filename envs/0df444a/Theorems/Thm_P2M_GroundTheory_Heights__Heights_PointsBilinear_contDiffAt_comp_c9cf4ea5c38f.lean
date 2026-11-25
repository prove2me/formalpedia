-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_contDiffAt_comp_c9cf4ea5c38f
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_contDiffAt_comp_c9cf4ea5c38f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:26.591987+00:00
-- url     : https://prove2.me/theorems/cb086d7b-9803-41ff-b13b-a6004468a29a
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear cont Diff At comp c9cf4ea5c38f: P2 M Ground Theory Heights  Heights Points Bilinear cont Diff At comp c9cf4ea5c38f
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear cont Diff At comp c9cf4ea5c38f construction uses the P2 M Ground Theory Heights  Heights Points Bilinear cont Diff At comp c9cf4ea5c38f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L20-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_contDiffAt_comp_c9cf4ea5c38f {D : ℕ} {u : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => u (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«contDiffAt_comp» := P2M_GroundTheory_Heights__Heights_PointsBilinear_contDiffAt_comp_c9cf4ea5c38f
