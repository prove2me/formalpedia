-- Prove2me | Theorems.Thm_PositivityTheory_RL_Up_taylor2
-- name    : PositivityTheory.RL.Up.taylor2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:59:45.46724+00:00
-- url     : https://prove2.me/theorems/3965f398-6d59-4885-8194-473b19892e4b
-- title:
--   Up: taylor2
-- statement:
--   The Up construction uses the taylor2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L24-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil

theorem PositivityTheory.RL.Up.taylor2 (φ φ' φ'' : ℝ → ℂ) (h1 : ∀ t, HasDerivAt φ (φ' t) t) (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖φ'' t‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ‖φ t - φ 0 - t * φ' 0‖ ≤ M * t ^ 2 := by sorry
