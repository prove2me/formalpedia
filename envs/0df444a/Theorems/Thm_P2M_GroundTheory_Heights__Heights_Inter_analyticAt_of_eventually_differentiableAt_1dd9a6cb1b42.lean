-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42
-- name    : P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:21.021092+00:00
-- url     : https://prove2.me/theorems/f94277ff-1a61-46d5-a194-cd1d7258d9cd
-- title:
--   P2 M Ground Theory Heights  Heights Inter analytic At of eventually differentiable At 1dd9a6cb1b42: P2 M Ground Theory Heights  Heights Inter analytic At of eventually differentiable At 1dd9a6cb1b42
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter analytic At of eventually differentiable At 1dd9a6cb1b42 construction uses the P2 M Ground Theory Heights  Heights Inter analytic At of eventually differentiable At 1dd9a6cb1b42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSheetHessPSD.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSheetHessPSD.lean#L16-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42 {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«analyticAt_of_eventually_differentiableAt» := P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42
