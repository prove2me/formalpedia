-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_one_lt_absNorm_real
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.one_lt_absNorm_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:10.112034+00:00
-- url     : https://prove2.me/theorems/63f3ced2-6a4b-4979-9aeb-9b52a63ad8ec
-- title:
--   Free Quotient Rank: one lt abs Norm real
-- statement:
--   The Free Quotient Rank construction uses the one lt abs Norm real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L26-L27

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by sorry
