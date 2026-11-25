-- Prove2me | Theorems.Thm_PositivityTheory_RL_Up_good_sup
-- name    : PositivityTheory.RL.Up.good_sup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:10.09182+00:00
-- url     : https://prove2.me/theorems/b06580f2-1531-4bd5-9150-c24932b9a8d3
-- title:
--   Up: good sup
-- statement:
--   The Up construction uses the good sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L73-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L73-L122

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
variable {l : Type} [Fintype l] [DecidableEq l]
omit [DecidableEq l]

theorem PositivityTheory.RL.Up.good_sup (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hm : ∀ s t, U (s + t) = U s * U t)
    (h1 : ∀ f, HasDerivAt (fun t => (U t f).toLp 2 volume) ((Q f).toLp 2 volume) 0)
    (hL : ∀ s, ∃ L : L2 l →L[ℂ] L2 l, ∀ f, (U s f).toLp 2 volume = L (f.toLp 2 volume))
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun t => T (U t f)) :
    Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ) := by sorry
