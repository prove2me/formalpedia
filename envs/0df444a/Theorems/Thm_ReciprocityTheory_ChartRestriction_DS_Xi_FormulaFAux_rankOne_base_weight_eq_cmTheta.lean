-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_rankOne_base_weight_eq_cmTheta
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.rankOne_base_weight_eq_cmTheta
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:53:37.146635+00:00
-- url     : https://prove2.me/theorems/c55d6d4f-b8e2-4c1e-bcc8-191ad2125003
-- title:
--   Formula FAux: rank One base weight eq cm Theta
-- statement:
--   The Formula FAux construction uses the rank One base weight eq cm Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L320-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L320-L321

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.rankOne_base_weight_eq_cmTheta (k r' : ℕ) (t : Fin (r' + 1)) (ht : ¬ t.val < r') (h : t.val < 2 * r' + k + 1) :
    (⟨t.val, h⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 := by sorry
