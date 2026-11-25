-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_exists_sphere_ge
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.exists_sphere_ge
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:06.925811+00:00
-- url     : https://prove2.me/theorems/0c31fd3a-83fa-463f-8774-3ee3ba1d02d9
-- title:
--   Plurisubharmonic Extension: exists sphere ge
-- statement:
--   The Plurisubharmonic Extension construction uses the exists sphere ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L315-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L315-L328

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

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.exists_sphere_ge {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (sphere 0 r)) (h : g 0 ≤ circleAverage g 0 r) :
    ∃ ζ ∈ sphere (0 : ℂ) r, g 0 ≤ g ζ := by sorry
