-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:12:36.113858+00:00
-- url     : https://prove2.me/theorems/52adb639-bbd7-45f2-bd19-54a4c7afd682
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff lead  3735fe896cb7: P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff lead  3735fe896cb7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff lead  3735fe896cb7 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Cas Ps B cont Diff lead  3735fe896cb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L65-L80

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7 (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (fun z : 𝕄 => lead i z) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«CasPsB».«contDiff_lead'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7
