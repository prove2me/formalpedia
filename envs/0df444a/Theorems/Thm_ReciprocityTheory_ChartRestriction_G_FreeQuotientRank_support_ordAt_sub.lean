-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_support_ordAt_sub
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.support_ordAt_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:47.054158+00:00
-- url     : https://prove2.me/theorems/e0b7ffce-766a-4c31-b934-d46d380b0c3d
-- title:
--   Free Quotient Rank: support ord At sub
-- statement:
--   The Free Quotient Rank construction uses the support ord At sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L44-L54

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.support_ordAt_sub {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v) ⊆
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖ := by sorry
