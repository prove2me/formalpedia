-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_pow
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:29.305609+00:00
-- url     : https://prove2.me/theorems/32ec5c16-6d3c-42c2-beb1-015baa043395
-- title:
--   Basis Change Pf: cb pow
-- statement:
--   The Basis Change Pf construction uses the cb pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L35-L40

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_pow {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by sorry
