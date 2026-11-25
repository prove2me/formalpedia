-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poisson_ext
-- name    : ReciprocityTheory.AnForm.A.poisson_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:07.748402+00:00
-- url     : https://prove2.me/theorems/f32d1884-49d4-58b8-a21a-285390bbe61c
-- title:
--   A: poisson ext
-- statement:
--   The A construction uses the poisson ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L378-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L378-L428

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

theorem ReciprocityTheory.AnForm.A.poisson_ext {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere 0 r)) :
    ∃ Φ : ℂ → ℝ, ContinuousOn Φ (Metric.closedBall 0 r) ∧ (∀ ζ ∈ Metric.sphere 0 r, Φ ζ = g ζ) ∧
      Φ 0 = Real.circleAverage g 0 r ∧
      ∀ a s, 0 < s → Metric.closedBall a s ⊆ Metric.ball 0 r → Real.circleAverage Φ a s = Φ a := by sorry
