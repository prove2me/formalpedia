-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_exists_unit_point
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.exists_unit_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:50.518478+00:00
-- url     : https://prove2.me/theorems/bed18f03-f858-4d61-990a-b9a05a55312f
-- title:
--   Unit Point Lift Ball: exists unit point
-- statement:
--   The Unit Point Lift Ball construction uses the exists unit point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L29-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L29-L116

import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.exists_unit_point (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K))
    (P δ : MvPolynomial ι K) (hP : ∀ μ, ‖coeff μ P‖ ≤ 1) (hP1 : ∃ μ, ‖coeff μ P‖ = 1)
    (hδ : ∀ μ, ‖coeff μ δ‖ ≤ 1) (hδ1 : ∃ μ, ‖coeff μ δ‖ = 1) :
    ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ = 1) ∧ ‖eval x P‖ = 1 ∧ ‖eval x δ‖ = 1 := by sorry
