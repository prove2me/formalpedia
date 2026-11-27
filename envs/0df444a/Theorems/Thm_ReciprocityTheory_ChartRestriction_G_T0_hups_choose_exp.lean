-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_choose_exp
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_choose_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:53.767555+00:00
-- url     : https://prove2.me/theorems/8910be92-5328-56de-97cb-afbb5a873110
-- title:
--   T0: hups choose exp
-- statement:
--   The T0 construction uses the hups choose exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L48-L66

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_choose_exp (n p a : ℕ) (hp : p ≤ n) :
    (((n + a).choose a : ℕ) : ℝ) ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by sorry
