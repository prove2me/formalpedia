-- Prove2me | Theorems.Thm_PIW_FdPA_rh_facts
-- name    : PIW.FdPA.rh_facts
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:54.803431+00:00
-- url     : https://prove2.me/theorems/953b892f-6e28-471d-a04b-93a6ddb1633e
-- title:
--   Fd PA: rh facts
-- statement:
--   The Fd PA construction uses the rh facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L48-L59

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

theorem PIW.FdPA.rh_facts {c1 w : ℝ} (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w < 1 / 10 ∧ w * d6rh c1 w ≤ 1 / 36 := by sorry
