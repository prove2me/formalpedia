-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_block_weights_integral
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.block_weights_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:42.837425+00:00
-- url     : https://prove2.me/theorems/0d4a2a32-af94-5aa8-849a-725c7cfb334b
-- title:
--   HW: block weights integral
-- statement:
--   The HW construction uses the block weights integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L149-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L149-L170

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.block_weights_integral {ε : Fin n → Bool} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {Λ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) (hw : IsKHWVec ε F Λ v)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, ε a = ε b → ∃ z : ℤ, (Λ + ν) a - (Λ + ν) b = z := by sorry
