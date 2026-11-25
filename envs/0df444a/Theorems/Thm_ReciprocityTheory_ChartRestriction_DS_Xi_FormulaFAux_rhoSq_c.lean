-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_rhoSq_c
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.rhoSq_c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:56.660806+00:00
-- url     : https://prove2.me/theorems/fbf4f32d-d4b5-55fc-a708-68e869a6e131
-- title:
--   Formula FAux: rho Sq c
-- statement:
--   The Formula FAux construction uses the rho Sq c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L347-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L347-L360

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.rhoSq_c (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (rhoSq (hcoord k r' x) l : ℂ) = (1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j) +
      Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0) := by sorry
