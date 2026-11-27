-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_ratio
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_ratio
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:55.819896+00:00
-- url     : https://prove2.me/theorems/fcb16eb6-a47a-58b4-a287-9dcc3008b443
-- title:
--   T0: hups ratio
-- statement:
--   The T0 construction uses the hups ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L70-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsChooseRatio.lean#L70-L215

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
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_ratio (D N n n' deF u del : ℕ) (h1 : 1 ≤ deF) (hdel : deF ≤ del)
    (hu : u ≤ (D + 1) * del) (hn : 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del ≤ n)
    (hn' : n' = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del) :
    (n : ℝ) * cardUX D N n n' ≤ ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by sorry
