-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_formulaF_all
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.formulaF_all
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:14:30.856582+00:00
-- url     : https://prove2.me/theorems/63d46c95-76e7-4c39-b72f-d31a59eef070
-- title:
--   Formula FAux: formula F all
-- statement:
--   The Formula FAux construction uses the formula F all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L202-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L202-L202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.formulaF_all : FormulaF := by sorry
