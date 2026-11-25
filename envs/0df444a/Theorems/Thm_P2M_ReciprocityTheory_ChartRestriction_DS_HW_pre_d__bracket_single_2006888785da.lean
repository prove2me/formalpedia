-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__bracket_single_2006888785da
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__bracket_single_2006888785da
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:35.0647+00:00
-- url     : https://prove2.me/theorems/1e0f07c7-c608-5599-a1a6-2df2f49471e6
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW pre d  bracket single 2006888785da: P2 M Reciprocity Theory Chart Restriction DS HW pre d  bracket single 2006888785da
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW pre d  bracket single 2006888785da construction uses the P2 M Reciprocity Theory Chart Restriction DS HW pre d  bracket single 2006888785da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L207-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelGenA.lean#L207-L214

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__bracket_single_2006888785da {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    dτ (Matrix.single a b 1) * dτ (Matrix.single c d 1) -
        dτ (Matrix.single c d 1) * dτ (Matrix.single a b 1) =
      dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«pre_dτ_bracket_single» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__bracket_single_2006888785da
