-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_entry_conj_single
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.entry_conj_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:52.32881+00:00
-- url     : https://prove2.me/theorems/fd51694a-11aa-47be-980b-1bceda358d7e
-- title:
--   Cas Ps A: entry conj single
-- statement:
--   The Cas Ps A construction uses the entry conj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsA.lean#L13-L15

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.entry_conj_single (u v : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (u * Matrix.single a b (1 : ℂ) * v) i j = u i a * v b j := by sorry
