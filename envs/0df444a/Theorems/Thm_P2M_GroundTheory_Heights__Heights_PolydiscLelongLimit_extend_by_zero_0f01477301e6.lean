-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_extend_by_zero_0f01477301e6
-- name    : P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_extend_by_zero_0f01477301e6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:20.268461+00:00
-- url     : https://prove2.me/theorems/d3f834e7-2176-48d8-87b3-f329461581f9
-- title:
--   P2 M Ground Theory Heights  Heights Polydisc Lelong Limit extend by zero 0f01477301e6: P2 M Ground Theory Heights  Heights Polydisc Lelong Limit extend by zero 0f01477301e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Polydisc Lelong Limit extend by zero 0f01477301e6 construction uses the P2 M Ground Theory Heights  Heights Polydisc Lelong Limit extend by zero 0f01477301e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L25-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L25-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit
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
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit

theorem P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_extend_by_zero_0f01477301e6 {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PolydiscLelongLimit».«extend_by_zero» := P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_extend_by_zero_0f01477301e6
