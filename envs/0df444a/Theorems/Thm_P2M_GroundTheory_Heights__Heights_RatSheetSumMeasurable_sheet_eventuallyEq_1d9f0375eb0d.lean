-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:57.371522+00:00
-- url     : https://prove2.me/theorems/6cf60637-2fd2-4423-846a-09b6f7527b9e
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable sheet eventually Eq 1d9f0375eb0d: P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable sheet eventually Eq 1d9f0375eb0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable sheet eventually Eq 1d9f0375eb0d construction uses the P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable sheet eventually Eq 1d9f0375eb0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L22-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ}
    (hs : RatChart.IsRatSheetAt J p q x s) (hs' : RatChart.IsRatSheetAt J p q x s') :
    s' =ᶠ[𝓝 (RatChart.ratMap p q x)] s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetSumMeasurable».«sheet_eventuallyEq» := P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d
