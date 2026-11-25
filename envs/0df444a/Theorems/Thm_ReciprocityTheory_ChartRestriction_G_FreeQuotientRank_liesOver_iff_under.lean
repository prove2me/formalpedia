-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_liesOver_iff_under
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.liesOver_iff_under
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:42.481867+00:00
-- url     : https://prove2.me/theorems/74e4fb75-0b99-502b-87d6-140035529a27
-- title:
--   Free Quotient Rank: lies Over iff under
-- statement:
--   The Free Quotient Rank construction uses the lies Over iff under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L64-L72

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.liesOver_iff_under (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) :
    LiesOver w la ↔ under (K := K) w = la := by sorry
