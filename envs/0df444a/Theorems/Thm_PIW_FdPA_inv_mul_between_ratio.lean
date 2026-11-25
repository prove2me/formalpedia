-- Prove2me | Theorems.Thm_PIW_FdPA_inv_mul_between_ratio
-- name    : PIW.FdPA.inv_mul_between_ratio
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:41.650771+00:00
-- url     : https://prove2.me/theorems/0a78af94-6418-461d-ad80-f0d3b86804aa
-- title:
--   Fd PA: inv mul between ratio
-- statement:
--   The Fd PA construction uses the inv mul between ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/DivLeExpOfAbsLogSubLe.lean#L9-L28

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

theorem PIW.FdPA.inv_mul_between_ratio {c m m0 ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hm0 : c * m0 = 1)
    (hlo : (1 - ρ) / (1 + ρ) * m0 ≤ m) (hhi : m ≤ (1 + ρ) / (1 - ρ) * m0) :
    (1 - ρ) / (1 + ρ) ≤ 1 / (c * m) ∧ 1 / (c * m) ≤ (1 + ρ) / (1 - ρ) := by sorry
