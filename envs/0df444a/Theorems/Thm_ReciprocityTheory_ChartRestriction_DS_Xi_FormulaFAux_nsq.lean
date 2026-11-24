-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_nsq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.nsq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:28.002057+00:00
-- url     : https://prove2.me/theorems/28711334-faf7-4ea3-a8c1-5ae0e45fbdef
-- title:
--   Formula FAux: nsq
-- statement:
--   The Formula FAux construction uses the nsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L270-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean#L270-L274

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.nsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by sorry
