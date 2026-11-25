-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowComp_lin_entry
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowComp_lin_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:19.806705+00:00
-- url     : https://prove2.me/theorems/bfe261d7-e4fc-55e8-8bc1-f10be590945e
-- title:
--   HW: low Comp lin entry
-- statement:
--   The HW construction uses the low Comp lin entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/LowComp.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/LowComp.lean#L57-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowComp_lin_entry {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) :
    lowCompLin (γ k) = lowCompLin (γ j) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by sorry
