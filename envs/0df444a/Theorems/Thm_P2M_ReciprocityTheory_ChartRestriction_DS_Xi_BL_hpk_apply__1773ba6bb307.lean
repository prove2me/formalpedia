-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:19.246949+00:00
-- url     : https://prove2.me/theorems/84476a58-6906-4b0e-99b6-7e6d3fa64fe5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi BL hpk apply  1773ba6bb307: P2 M Reciprocity Theory Chart Restriction DS Xi BL hpk apply  1773ba6bb307
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi BL hpk apply  1773ba6bb307 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi BL hpk apply  1773ba6bb307 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L51-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307 (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«BL».«hpk_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307
