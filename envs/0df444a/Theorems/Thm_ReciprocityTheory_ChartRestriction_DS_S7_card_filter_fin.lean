-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_card_filter_fin
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.card_filter_fin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:44.402523+00:00
-- url     : https://prove2.me/theorems/7aa62dc5-3523-50a1-8103-c1af7b6de260
-- title:
--   S7: card filter fin
-- statement:
--   The S7 construction uses the card filter fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L175-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L175-L186

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.card_filter_fin {N : ℕ} (Q : Fin N → Prop) [DecidablePred Q] (lo hi : ℕ) (hhi : hi ≤ N)
    (hQ : ∀ b : Fin N, Q b ↔ lo ≤ (b : ℕ) ∧ (b : ℕ) < hi) : (univ.filter Q).card = hi - lo := by sorry
