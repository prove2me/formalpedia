-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_pert_submean
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_submean
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:02.674829+00:00
-- url     : https://prove2.me/theorems/8dc7391e-bc91-4d73-b5be-ff4faa6efdd9
-- title:
--   Plurisubharmonic Extension: pert submean
-- statement:
--   The Plurisubharmonic Extension construction uses the pert submean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L126-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L126-L169

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

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_submean {E : Finset ℂ} {c a : ℂ} {s ε δ : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (haE : a ∉ E) (hE : ∀ f ∈ E, f ∉ sphere a s) :
    CircleIntegrable (pert E c ε δ) a s ∧
      pert E c ε δ a + δ * s ^ 2 ≤ circleAverage (pert E c ε δ) a s := by sorry
