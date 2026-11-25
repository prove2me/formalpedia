-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_lin
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:55.910392+00:00
-- url     : https://prove2.me/theorems/c94bd71b-1e44-5ea7-a538-de0096f54043
-- title:
--   Basis Change Pf: cb lin
-- statement:
--   The Basis Change Pf construction uses the cb lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L59-L68

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_lin [Fintype ι] (A : ι → ι → K) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i k, ‖A i k‖ ≤ c) (i : ι) :
    CB (∑ k, C (A i k) * X k) c := by sorry
