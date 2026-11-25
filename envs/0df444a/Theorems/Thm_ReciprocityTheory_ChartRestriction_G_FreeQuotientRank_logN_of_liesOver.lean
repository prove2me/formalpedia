-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_logN_of_liesOver
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.logN_of_liesOver
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:17.079658+00:00
-- url     : https://prove2.me/theorems/b61bf21f-f4ab-4b68-95fe-f7eb8fd3d989
-- title:
--   Free Quotient Rank: log N of lies Over
-- statement:
--   The Free Quotient Rank construction uses the log N of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L74-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
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
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.logN_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {la : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w la) : logN w = (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * logN la := by sorry
