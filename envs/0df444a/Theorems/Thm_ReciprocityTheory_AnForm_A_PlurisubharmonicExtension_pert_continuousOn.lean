-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_pert_continuousOn
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_continuousOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:43.692129+00:00
-- url     : https://prove2.me/theorems/81be31e8-53d6-5715-8dff-c071cc6f99cb
-- title:
--   Plurisubharmonic Extension: pert continuous On
-- statement:
--   The Plurisubharmonic Extension construction uses the pert continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L115-L124

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

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_continuousOn (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) :
    ContinuousOn (pert E c ε δ) (↑E)ᶜ := by sorry
