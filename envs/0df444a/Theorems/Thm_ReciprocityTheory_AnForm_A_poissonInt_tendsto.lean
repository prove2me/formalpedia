-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_tendsto
-- name    : ReciprocityTheory.AnForm.A.poissonInt_tendsto
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:20.717948+00:00
-- url     : https://prove2.me/theorems/f90bd08e-67a4-5991-9830-2f24cc8b97b9
-- title:
--   A: poisson Int tendsto
-- statement:
--   The A construction uses the poisson Int tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L268-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L268-L376

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

theorem ReciprocityTheory.AnForm.A.poissonInt_tendsto {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) r) :
    Tendsto (poissonInt g r) (𝓝[ball 0 r] ζ₀) (𝓝 (g ζ₀)) := by sorry
