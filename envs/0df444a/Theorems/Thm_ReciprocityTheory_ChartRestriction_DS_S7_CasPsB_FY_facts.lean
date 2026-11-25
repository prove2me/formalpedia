-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_FY_facts
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.FY_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:22.63637+00:00
-- url     : https://prove2.me/theorems/1b909f23-6710-493f-8d09-fb1f6d2586da
-- title:
--   Cas Ps B: FY facts
-- statement:
--   The Cas Ps B construction uses the FY facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L117-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L117-L139

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.FY_facts (T : KType ε Λ) (μ : Fin n → ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => FY T μ Y y k) (FY' T μ Y x k) x ∧
      ∀ H : 𝕄, FY' T μ Y x k H =
        (fderiv ℂ (Ps1.PhiP μ) (Matrix.of.symm (toMK k⁻¹ * x * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Y * Matrix.of H * toMK k)) +
          fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) (Matrix.of.symm (toMK k⁻¹ * x * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Matrix.of H * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Y * x * toMK k))) • (T.op k * projW T * T.op k⁻¹) := by sorry
