-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_sub
-- name    : ReciprocityTheory.AnForm.A.poissonInt_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:25.185337+00:00
-- url     : https://prove2.me/theorems/d056be77-d330-48af-81b9-e8db655639d5
-- title:
--   A: poisson Int sub
-- statement:
--   The A construction uses the poisson Int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L242-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L242-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

theorem ReciprocityTheory.AnForm.A.poissonInt_sub {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    poissonInt g r w - c =
      Real.circleAverage (fun z ↦ poissonKernel 0 w z * (g z - c)) 0 r := by sorry
