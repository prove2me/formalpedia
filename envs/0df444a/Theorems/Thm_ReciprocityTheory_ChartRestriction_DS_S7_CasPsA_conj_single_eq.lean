-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_conj_single_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.conj_single_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:00.968811+00:00
-- url     : https://prove2.me/theorems/22e7ba3a-57a3-42ec-a6f7-393ae18bdec6
-- title:
--   Cas Ps A: conj single eq
-- statement:
--   The Cas Ps A construction uses the conj single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L17-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.conj_single_eq (u v : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    u * Matrix.single a b (1 : ℂ) * v = ∑ c, ∑ d, (u c a * v b d) • Matrix.single c d (1 : ℂ) := by sorry
