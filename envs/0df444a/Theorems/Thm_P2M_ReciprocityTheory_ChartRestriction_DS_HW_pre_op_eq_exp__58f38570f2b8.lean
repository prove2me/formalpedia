-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_eq_exp__58f38570f2b8
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_eq_exp__58f38570f2b8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:14:50.23439+00:00
-- url     : https://prove2.me/theorems/1360dcc1-7782-4f12-a5aa-72429631b9e6
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW pre op eq exp  58f38570f2b8: P2 M Reciprocity Theory Chart Restriction DS HW pre op eq exp  58f38570f2b8
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW pre op eq exp  58f38570f2b8 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW pre op eq exp  58f38570f2b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L96-L107

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
include hder

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_eq_exp__58f38570f2b8 (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ preOp τ k = NormedSpace.exp (dτ Y) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«pre_op_eq_exp'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_eq_exp__58f38570f2b8
