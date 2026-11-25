-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_smg
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.smg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:05.345051+00:00
-- url     : https://prove2.me/theorems/9a69c251-f454-411d-b874-15c3624957db
-- title:
--   Plurisubharmonic Extension: smg
-- statement:
--   The Plurisubharmonic Extension construction uses the smg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L295-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L295-L313

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.smg {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hB : ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, g ζ ≤ B)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by sorry
