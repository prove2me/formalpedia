-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_contDiffAt_F_02c255d304b9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_contDiffAt_F_02c255d304b9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:31.333588+00:00
-- url     : https://prove2.me/theorems/182dc435-1f3b-4a91-8cba-561193178e90
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature cont Diff At F 02c255d304b9: P2 M Ground Theory Heights  Heights Inter Regularized Curvature cont Diff At F 02c255d304b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature cont Diff At F 02c255d304b9 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature cont Diff At F 02c255d304b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L244-L250

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_contDiffAt_F_02c255d304b9 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«contDiffAt_F» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_contDiffAt_F_02c255d304b9
