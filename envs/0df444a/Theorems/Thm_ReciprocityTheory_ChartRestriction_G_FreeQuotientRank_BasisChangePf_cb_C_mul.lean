-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_C_mul
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:31.123439+00:00
-- url     : https://prove2.me/theorems/91d739f1-0aa0-492d-8692-4426d3c6389e
-- title:
--   Basis Change Pf: cb C mul
-- statement:
--   The Basis Change Pf construction uses the cb C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L53-L57

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_C_mul (a : K) {Q : MvPolynomial ι K} {c : ℝ} (hQ : CB Q c) : CB (C a * Q) (‖a‖ * c) := by sorry
