-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerUnitDensity_matrixEntry_eq_one
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerUnitDensity_matrixEntry_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:22.117912+00:00
-- url     : https://prove2.me/theorems/6ddcc580-91ab-4bba-bbff-8cebda2b1b65
-- title:
--   Finite Instrument: tensor Power Unit Density matrix Entry eq one
-- statement:
--   The unique depth-zero matrix entry of any tensor-unit density is one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L103-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/SelectedBranchOperator.lean#L103-L121

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerUnitDensity_matrixEntry_eq_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {β : Type v} [Fintype β]
    (basis : OrthonormalBasis β Complex H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    inner Complex (tensorPowerBasis basis 0 PUnit.unit)
        (rhoUnit.toOperator (tensorPowerBasis basis 0 PUnit.unit)) = 1 := by sorry
