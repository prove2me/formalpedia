-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuous_FY__2f2bcbf33dc7
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuous_FY__2f2bcbf33dc7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:38.192808+00:00
-- url     : https://prove2.me/theorems/bfe8069d-fbf5-42f5-875c-956c204bc8ce
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B continuous FY  2f2bcbf33dc7: P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B continuous FY  2f2bcbf33dc7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B continuous FY  2f2bcbf33dc7 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B continuous FY  2f2bcbf33dc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L220-L224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
variable [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
variable (hU : IsOpen U) (hΩ : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
  (hfd : ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
          (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
include hU hΩ hfd

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuous_FY__2f2bcbf33dc7 (Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U) :
    Continuous (FY' T μ Y z) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«CasPsB».«continuous_FY'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuous_FY__2f2bcbf33dc7
