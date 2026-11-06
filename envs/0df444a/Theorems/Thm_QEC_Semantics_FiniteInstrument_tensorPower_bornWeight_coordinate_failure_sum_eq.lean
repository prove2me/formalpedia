-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_bornWeight_coordinate_failure_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_coordinate_failure_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:57.705529+00:00
-- url     : https://prove2.me/theorems/2cc8dd61-3b33-4e90-915b-2fb4f888d9e3
-- title:
--   Finite Instrument: tensor Power born Weight coordinate failure sum eq
-- statement:
--   The Born mass of a failure event on one selected coordinate is exactly
--   the base-instrument failure mass on that coordinate's true marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L432-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L432-L505

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_coordinate_failure_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (attempts : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts))
    (trial : Fin attempts) :
    (∑ history ∈ Finset.univ.filter (fun history : tensorPowerHistory Omega attempts =>
        fails (tensorPowerHistoryAt Omega attempts history trial)),
      (I.tensorPower attempts).bornWeight history rho) =
      ∑ outcome ∈ Finset.univ.filter fails,
        I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by sorry
