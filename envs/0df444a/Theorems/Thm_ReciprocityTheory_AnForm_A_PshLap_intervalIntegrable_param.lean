-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_intervalIntegrable_param
-- name    : ReciprocityTheory.AnForm.A.PshLap.intervalIntegrable_param
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:08.740978+00:00
-- url     : https://prove2.me/theorems/9f027dcf-5b86-4cb4-82ad-259111c33d92
-- title:
--   Psh Lap: interval Integrable param
-- statement:
--   The Psh Lap construction uses the interval Integrable param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L133-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L133-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section

theorem ReciprocityTheory.AnForm.A.PshLap.intervalIntegrable_param {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    IntervalIntegrable (fun x => ∫ y in c..d, F x y) volume a b := by sorry
