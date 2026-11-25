-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_disc_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.disc_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:08.727133+00:00
-- url     : https://prove2.me/theorems/646b1073-bdc4-4b1c-98b8-c0dc46357837
-- title:
--   Free Quotient Rank: disc bound
-- statement:
--   The Free Quotient Rank construction uses the disc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DiscPf.lean#L6-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DiscPf.lean#L6-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_CauchyInequalityOnTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.disc_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (c : ℤ → K)
    (S : Set K)
    (hc : ∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1)
    (t : K) (htS : t ∈ S) (n : ℤ) : ‖c n‖ * ‖t‖ ^ n ≤ 1 := by sorry
