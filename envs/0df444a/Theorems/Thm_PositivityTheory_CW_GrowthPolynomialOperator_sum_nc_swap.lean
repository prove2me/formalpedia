-- Prove2me | Theorems.Thm_PositivityTheory_CW_GrowthPolynomialOperator_sum_nc_swap
-- name    : PositivityTheory.CW.GrowthPolynomialOperator.sum_nc_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:08.911308+00:00
-- url     : https://prove2.me/theorems/1134c8dd-a227-544e-ba59-efd1563606e4
-- title:
--   Growth Polynomial Operator: sum nc swap
-- statement:
--   The Growth Polynomial Operator construction uses the sum nc swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GrowthOfBasic.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GrowthOfBasic.lean#L18-L20

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthOfBasic
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
open PositivityTheory.CW.GrowthPolynomialOperator
variable {n : ℕ}

theorem PositivityTheory.CW.GrowthPolynomialOperator.sum_nc_swap {β : Type*} [AddCommMonoid β] (ε : Fin n → Bool) (g : Fin n × Fin n → β) :
    ∑ p ∈ nc ε, g p.swap = ∑ p ∈ nc ε, g p := by sorry
