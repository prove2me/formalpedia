-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Chart_phi_mem
-- name    : PI.SwSandwichOfWork.Chart_phi_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:14.91255+00:00
-- url     : https://prove2.me/theorems/1e09c76f-057e-4ec0-a856-d3a2f4ee732b
-- title:
--   Sw Sandwich Of Work: Chart phi mem
-- statement:
--   The Sw Sandwich Of Work construction uses the Chart phi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L45-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L45-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}

theorem PI.SwSandwichOfWork.Chart_phi_mem (hBC : BigCellG) (hPF : PhiForm) (hLW : LieWb) (hEN : ExpN)
    {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (hx : ‖v.2.1‖ < 1) :
    PhiP k r v ∈ UH (Hpk k r) := by sorry
