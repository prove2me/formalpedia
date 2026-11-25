-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_eval_lift
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.eval_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:10.876233+00:00
-- url     : https://prove2.me/theorems/4af8787a-c846-42a5-8ca5-4ab5c521ff3c
-- title:
--   Unit Point Lift Ball: eval lift
-- statement:
--   The Unit Point Lift Ball construction uses the eval lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/UnitPointLiftBall.lean#L21-L27

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.eval_lift (PO : MvPolynomial ι (unitBallRing K)) (σ : ι → unitBallRing K) :
    eval (fun i => (σ i : K)) (MvPolynomial.map (unitBallRing K).subtype PO) =
      ((eval σ PO : unitBallRing K) : K) := by sorry
