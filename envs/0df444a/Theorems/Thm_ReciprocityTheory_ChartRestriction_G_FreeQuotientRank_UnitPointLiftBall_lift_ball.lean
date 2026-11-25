-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_lift_ball
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.lift_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:01.102338+00:00
-- url     : https://prove2.me/theorems/6a1e66f4-5d0a-4388-85a3-bd8dc9d13c25
-- title:
--   Unit Point Lift Ball: lift ball
-- statement:
--   The Unit Point Lift Ball construction uses the lift ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L9-L19

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.lift_ball (P : MvPolynomial ι K) (hP : ∀ μ, ‖coeff μ P‖ ≤ 1) :
    ∃ PO : MvPolynomial ι (unitBallRing K), MvPolynomial.map (unitBallRing K).subtype PO = P := by sorry
