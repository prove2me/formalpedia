-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_single_mul_single__6f664d746993
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_single_mul_single__6f664d746993
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:45.381408+00:00
-- url     : https://prove2.me/theorems/35981d9a-799f-5739-8944-0737cc7fc5c4
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Cap Phi single mul single  6f664d746993: P2 M Reciprocity Theory Chart Restriction DS S7 Cap Phi single mul single  6f664d746993
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Cap Phi single mul single  6f664d746993 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Cap Phi single mul single  6f664d746993 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L47-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
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
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_single_mul_single__6f664d746993 (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«CapPhi».«single_mul_single'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_single_mul_single__6f664d746993
