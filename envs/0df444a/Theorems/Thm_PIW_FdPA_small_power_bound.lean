-- Prove2me | Theorems.Thm_PIW_FdPA_small_power_bound
-- name    : PIW.FdPA.small_power_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:42.429888+00:00
-- url     : https://prove2.me/theorems/bca4e316-3440-4680-8009-22729aaebc24
-- title:
--   Fd PA: small power bound
-- statement:
--   The Fd PA construction uses the small power bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L39-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section

theorem PIW.FdPA.small_power_bound {w r rh z : ℝ} (hr0 : 0 ≤ r) (hrw : r ≤ w) (hw : 0 ≤ w) (hrh : 0 ≤ rh)
    (hwrh : w * rh ≤ 1 / 36) (hz0 : 0 ≤ z) (hz : z ≤ rh) : 4 * w * r * z ^ 2 ≤ 1 / 4 := by sorry
