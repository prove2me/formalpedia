-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_filteredBranchMeasuredTrace_mono
-- name    : QEC.Semantics.FiniteInstrument.filteredBranchMeasuredTrace_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:22.814512+00:00
-- url     : https://prove2.me/theorems/608b7900-3467-4300-8f4a-151b09db654c
-- title:
--   Finite Instrument: filtered Branch Measured Trace mono
-- statement:
--   If one visible event implies another, every physical measurement of the
--   first unnormalized branch has at most the measured mass of the second.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/FilteredBranchMeasurement.lean#L50-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/FilteredBranchMeasurement.lean#L50-L96

import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.FiniteInstrument
open Classical
open scoped BigOperators
universe u v w x y
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {mu : Type x} [Fintype mu]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.filteredBranchMeasuredTrace_mono
    (I : FiniteInstrument kappa Omega H K)
    (rho : DensityOperator H)
    (channel : QuantumChannel K L)
    (measurement : FiniteInstrument mu Xi L L)
    (measurementOutcome : Xi)
    (small large : Omega -> Prop)
    [DecidablePred small] [DecidablePred large]
    (himp : forall outcome, small outcome -> large outcome) :
    Complex.re (LinearMap.trace Complex L
      (measurement.branchOperator measurementOutcome
        (channel (filteredBranchOperatorSum I small rho.toOperator)))) <=
    Complex.re (LinearMap.trace Complex L
      (measurement.branchOperator measurementOutcome
        (channel (filteredBranchOperatorSum I large rho.toOperator)))) := by sorry
