-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowest_weight_differences_nat
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowest_weight_differences_nat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:34.497574+00:00
-- url     : https://prove2.me/theorems/6aeb6137-1a51-59f4-bd31-1051fb8901fc
-- title:
--   HW: lowest weight differences nat
-- statement:
--   The HW construction uses the lowest weight differences nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L133-L147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowest_weight_differences_nat {ε : Fin n → Bool} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, ν b - ν a = m := by sorry
