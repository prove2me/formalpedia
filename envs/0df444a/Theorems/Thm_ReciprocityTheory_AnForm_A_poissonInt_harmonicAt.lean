-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_harmonicAt
-- name    : ReciprocityTheory.AnForm.A.poissonInt_harmonicAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:17.924104+00:00
-- url     : https://prove2.me/theorems/7118d67c-a1c9-5245-a839-69104227c8d0
-- title:
--   A: poisson Int harmonic At
-- statement:
--   The A construction uses the poisson Int harmonic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L202-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L202-L229

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

theorem ReciprocityTheory.AnForm.A.poissonInt_harmonicAt {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) : HarmonicAt (poissonInt g r) w := by sorry
