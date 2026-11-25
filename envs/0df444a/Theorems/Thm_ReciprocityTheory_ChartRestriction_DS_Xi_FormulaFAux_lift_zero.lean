-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_lift_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.lift_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:13.958643+00:00
-- url     : https://prove2.me/theorems/78c8d802-48c7-53b8-bf5c-9349037952c3
-- title:
--   Formula FAux: lift zero
-- statement:
--   The Formula FAux construction uses the lift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermMatrixMulVecFirst.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermMatrixMulVecFirst.lean#L68-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.lift_zero (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p ∉ Set.range (levPos k 1 r')) : liftVec k 1 r' v p = 0 := by sorry
