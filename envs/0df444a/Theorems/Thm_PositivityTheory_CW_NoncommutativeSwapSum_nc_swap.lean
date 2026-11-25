-- Prove2me | Theorems.Thm_PositivityTheory_CW_NoncommutativeSwapSum_nc_swap
-- name    : PositivityTheory.CW.NoncommutativeSwapSum.nc_swap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:12.592615+00:00
-- url     : https://prove2.me/theorems/8d726727-4429-41b8-b7c4-5ec97f8a94c6
-- title:
--   Noncommutative Swap Sum: nc swap
-- statement:
--   The Noncommutative Swap Sum construction uses the nc swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GrowthPolynomialOperator.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GrowthPolynomialOperator.lean#L11-L13

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthPolynomialOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.NoncommutativeSwapSum

theorem PositivityTheory.CW.NoncommutativeSwapSum.nc_swap {n : ℕ} {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p.swap = ∑ p ∈ nc ε, f p := by sorry
