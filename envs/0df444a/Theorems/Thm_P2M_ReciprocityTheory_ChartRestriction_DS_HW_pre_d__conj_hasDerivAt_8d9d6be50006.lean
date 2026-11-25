-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__conj_hasDerivAt_8d9d6be50006
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__conj_hasDerivAt_8d9d6be50006
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:14:26.396851+00:00
-- url     : https://prove2.me/theorems/42191efe-2b27-4251-8a34-474b87bddecd
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW pre d  conj has Deriv At 8d9d6be50006: P2 M Reciprocity Theory Chart Restriction DS HW pre d  conj has Deriv At 8d9d6be50006
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW pre d  conj has Deriv At 8d9d6be50006 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW pre d  conj has Deriv At 8d9d6be50006 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L168-L173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA
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
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__conj_hasDerivAt_8d9d6be50006 (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (dτ (X * Y - Y * X)) 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«pre_dτ_conj_hasDerivAt» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__conj_hasDerivAt_8d9d6be50006
