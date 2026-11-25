-- Prove2me | Theorems.Thm_UnipMove_MajH_key_ineq
-- name    : UnipMove.MajH.key_ineq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:45.857493+00:00
-- url     : https://prove2.me/theorems/3f6a068f-d160-41b5-a22d-4cd26f505ea8
-- title:
--   Maj H: key ineq
-- statement:
--   The Maj H construction uses the key ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L54-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean#L54-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section

theorem UnipMove.MajH.key_ineq {A Bn u w D ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ Bn) (hu0 : 0 ≤ u) (hw0 : 0 ≤ w)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hu : u ≤ ρ * A) (hw : w ≤ ρ * Bn) (h1 : |D| ≤ u * Bn)
    (h2 : |D| ≤ A * w) :
    (1 - ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) ≤
        (1 + ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ∧
      (1 - ρ) * (A ^ 2 - u ^ 2 + Bn ^ 2 - w ^ 2) ≤
        (1 + ρ) * (A ^ 2 + w ^ 2 + 2 * D + (u ^ 2 + Bn ^ 2 + 2 * D)) := by sorry
