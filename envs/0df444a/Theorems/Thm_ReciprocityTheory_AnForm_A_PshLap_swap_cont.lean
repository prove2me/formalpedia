-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_swap_cont
-- name    : ReciprocityTheory.AnForm.A.PshLap.swap_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:10.905799+00:00
-- url     : https://prove2.me/theorems/6eb425a4-960a-4c26-9365-0d881fe5f798
-- title:
--   Psh Lap: swap cont
-- statement:
--   The Psh Lap construction uses the swap cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L122-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L122-L131

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

theorem ReciprocityTheory.AnForm.A.PshLap.swap_cont {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by sorry
