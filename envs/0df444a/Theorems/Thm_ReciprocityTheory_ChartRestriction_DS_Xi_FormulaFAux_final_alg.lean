-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_final_alg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.final_alg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:23.523294+00:00
-- url     : https://prove2.me/theorems/5bd2bf4b-98e1-432c-81a6-124bd6bf88eb
-- title:
--   Formula FAux: final alg
-- statement:
--   The Formula FAux construction uses the final alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L256-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergDualBaseVectorFormula.lean#L256-L292

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.final_alg (N m : ℕ) (hm : m ≤ N) (A A' : ℕ → ℂ) (Uu b : ℂ) :
    let x : ℕ → ℂ := fun j => A' j - b * A j
    (1 + (∑ j ∈ Finset.range N, (star (A j) * A j + star (A' j) * A' j) + Uu + b * star b) -
        ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (A j) * A j) +
      (∑ j ∈ Finset.range m, star (x j) * A j) * (∑ j ∈ Finset.range m, star (A j) * x j) =
    (1 + ∑ j ∈ Finset.range m, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range N, star (A j) * A j) + Uu +
        ∑ j ∈ Finset.range N, (if m ≤ j then star (A' j) * A' j else 0)) +
      (b + ∑ j ∈ Finset.range m, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range m, A' j * star (A j)) := by sorry
