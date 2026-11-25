-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_sum_lt_split
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.sum_lt_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:48.477167+00:00
-- url     : https://prove2.me/theorems/93d35d45-b8c4-42dd-9d96-4a29a35755fe
-- title:
--   Formula FAux: sum lt split
-- statement:
--   The Formula FAux construction uses the sum lt split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L247-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L247-L254

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.sum_lt_split (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range m, f j + ∑ j ∈ Finset.range N, (if m ≤ j then f j else 0) := by sorry
