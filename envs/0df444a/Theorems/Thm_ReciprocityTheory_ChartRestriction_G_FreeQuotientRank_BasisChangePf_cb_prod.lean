-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_prod
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:10.765822+00:00
-- url     : https://prove2.me/theorems/e969623a-35f3-42de-bff2-574aae21fbef
-- title:
--   Basis Change Pf: cb prod
-- statement:
--   The Basis Change Pf construction uses the cb prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L42-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf
open MvPolynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_prod {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by sorry
