-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finite_ordAt
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finite_ordAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:26.060626+00:00
-- url     : https://prove2.me/theorems/846c49fb-263b-45b4-9bf0-0024fee320b0
-- title:
--   Free Quotient Rank: finite ord At
-- statement:
--   The Free Quotient Rank construction uses the finite ord At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L56-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finite_ordAt {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite := by sorry
