-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_coef_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_coef_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:34.829565+00:00
-- url     : https://prove2.me/theorems/3c268c35-9ed4-5fa4-bdab-54a66762b995
-- title:
--   Cas Ps A: sum coef conj
-- statement:
--   The Cas Ps A construction uses the sum coef conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L23-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_coef_conj (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) (c d : Fin n) :
    ∑ a, ∑ b, (u c a * v b d) • (u * Matrix.single b a (1 : ℂ) * v) = Matrix.single d c (1 : ℂ) := by sorry
