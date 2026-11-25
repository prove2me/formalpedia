-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_op
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_op
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:08.366261+00:00
-- url     : https://prove2.me/theorems/54fc862a-67e5-412a-9343-4f61d39587eb
-- title:
--   S7: has Deriv At op
-- statement:
--   The S7 construction uses the has Deriv At op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DTauFacts.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DTauFacts.lean#L154-L162

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_op (T : KType ε Λ) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => T.op (k * γ t)) (T.op k * T.dτ Y) 0 := by sorry
