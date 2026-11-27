-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_CountPf_ratio
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf.ratio
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:08.112144+00:00
-- url     : https://prove2.me/theorems/1d409c91-8800-4d42-8d13-338c0c6bdd2b
-- title:
--   Count Pf: ratio
-- statement:
--   The Count Pf construction uses the ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CountPf.lean#L7-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CountPf.lean#L7-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountRhoPArithStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf.ratio (T c : ℕ) (hT : 0 < T) : ∀ k : ℕ,
    (1 - (k : ℝ) * c / T) * ((T + c + k).choose k : ℝ) ≤ ((T + k).choose k : ℝ) := by sorry
