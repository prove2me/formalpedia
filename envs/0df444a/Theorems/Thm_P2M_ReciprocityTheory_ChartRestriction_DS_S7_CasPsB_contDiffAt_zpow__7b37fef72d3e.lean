-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:12:05.769862+00:00
-- url     : https://prove2.me/theorems/b3def1f1-bbec-4e23-9826-4a65df13219f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff At zpow  7b37fef72d3e: P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff At zpow  7b37fef72d3e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff At zpow  7b37fef72d3e construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff At zpow  7b37fef72d3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L82-L87

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e {f : 𝕄 → ℂ} {x : 𝕄} {m : ℕ∞ω}
    (hf : ContDiffAt ℂ m f x) (hx : f x ≠ 0) (k : ℤ) : ContDiffAt ℂ m (fun y => f y ^ k) x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«CasPsB».«contDiffAt_zpow'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e
