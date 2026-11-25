-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_bilin_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_bilin_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:28.618189+00:00
-- url     : https://prove2.me/theorems/9e6a39c2-1f38-5924-aeb6-b6fede085e96
-- title:
--   Cas Ps A: sum bilin conj
-- statement:
--   The Cas Ps A construction uses the sum bilin conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L47-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_bilin_conj (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) :
    ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v) =
      ∑ a, ∑ b, B (Matrix.single a b 1) (Matrix.single b a 1) := by sorry
