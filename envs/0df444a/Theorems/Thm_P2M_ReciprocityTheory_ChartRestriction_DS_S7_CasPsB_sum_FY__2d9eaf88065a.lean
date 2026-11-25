-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_sum_FY__2d9eaf88065a
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_sum_FY__2d9eaf88065a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:12:26.49783+00:00
-- url     : https://prove2.me/theorems/f9c115e8-50de-4923-9530-a8ae3d3b2422
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B sum FY  2d9eaf88065a: P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B sum FY  2d9eaf88065a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B sum FY  2d9eaf88065a construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B sum FY  2d9eaf88065a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L236-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L236-L316

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_sum_FY__2d9eaf88065a (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ)
    {z : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hz : toMK k⁻¹ * z * toMK k ∈ OmegaSet n) :
    ∑ a, ∑ b, FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) =
      ((casVal lam : ℝ) : ℂ) • (PhiM μ (toMK k⁻¹ * z * toMK k) • (T.op k * projW T * T.op k⁻¹)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«CasPsB».«sum_FY'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_sum_FY__2d9eaf88065a
