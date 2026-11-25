-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_pars1__8f9192c16c33
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_pars1__8f9192c16c33
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:57:55.125225+00:00
-- url     : https://prove2.me/theorems/098b388a-6742-425d-a39f-24184dc1e83f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Formula FAux pars1  8f9192c16c33: P2 M Reciprocity Theory Chart Restriction DS Xi Formula FAux pars1  8f9192c16c33
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Formula FAux pars1  8f9192c16c33 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Formula FAux pars1  8f9192c16c33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L179-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L179-L227

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_pars1__8f9192c16c33 (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    star y ⬝ᵥ y = ∑ j ∈ Finset.range (r' + 1), (star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) +
      Uu k r' y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«FormulaFAux».«pars1'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_pars1__8f9192c16c33
