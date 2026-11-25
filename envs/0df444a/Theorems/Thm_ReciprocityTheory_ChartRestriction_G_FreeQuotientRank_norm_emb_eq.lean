-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_norm_emb_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.norm_emb_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:37.041889+00:00
-- url     : https://prove2.me/theorems/432162ff-f5cd-595b-8b17-c510885d4fa9
-- title:
--   Free Quotient Rank: norm emb eq
-- statement:
--   The Free Quotient Rank construction uses the norm emb eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L16-L24

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.norm_emb_eq (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordAt v x)) := by sorry
