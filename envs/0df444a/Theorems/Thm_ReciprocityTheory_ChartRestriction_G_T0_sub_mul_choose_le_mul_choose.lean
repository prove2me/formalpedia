-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sub_mul_choose_le_mul_choose
-- name    : ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:36.227047+00:00
-- url     : https://prove2.me/theorems/df5e94d7-7b09-45a7-8bcf-2e3fe41f1657
-- title:
--   T0: sub mul choose le mul choose
-- statement:
--   The T0 construction uses the sub mul choose le mul choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BinomRatio.lean#L12-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BinomRatio.lean#L12-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0

theorem ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by sorry
