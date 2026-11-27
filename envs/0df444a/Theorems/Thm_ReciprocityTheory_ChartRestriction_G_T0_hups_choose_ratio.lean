-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_choose_ratio
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_choose_ratio
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:26.532454+00:00
-- url     : https://prove2.me/theorems/2404799f-8c11-4c84-9bd1-5137987e8775
-- title:
--   T0: hups choose ratio
-- statement:
--   The T0 construction uses the hups choose ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L5-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_choose_ratio (n p : ℕ) (hp : p ≤ n) : ∀ a : ℕ,
    (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by sorry
