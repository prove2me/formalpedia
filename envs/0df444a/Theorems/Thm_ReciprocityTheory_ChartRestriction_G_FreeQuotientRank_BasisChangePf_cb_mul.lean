-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_mul
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:31.431283+00:00
-- url     : https://prove2.me/theorems/e81a5a14-d584-4d74-aa28-541e26a5c815
-- title:
--   Basis Change Pf: cb mul
-- statement:
--   The Basis Change Pf construction uses the cb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean#L20-L27

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf.cb_mul {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by sorry
