-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_gram_Y
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.gram_Y
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:12.529775+00:00
-- url     : https://prove2.me/theorems/f2b15847-82b1-4569-b669-1fcca3263a5f
-- title:
--   Formula FAux: gram Y
-- statement:
--   The Formula FAux construction uses the gram Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L229-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L229-L268

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.gram_Y (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => heis0 k r' x *ᵥ phiV k (1 + r') a) =
      (let A := AN k r' x.1; let A' := AN' k r' x.1; let b := hb k r' x.1 x.2
       (1 + ∑ j ∈ Finset.range l.val, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range (r' + 1), star (A j) * A j) +
          Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (A' j) * A' j else 0)) +
        (b + ∑ j ∈ Finset.range l.val, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range l.val, A' j * star (A j))).re := by sorry
