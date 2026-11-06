-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_bornWeight_coordinate_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_coordinate_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:03.459472+00:00
-- url     : https://prove2.me/theorems/9dbcf4a1-2160-4cb5-84ed-c941a2401764
-- title:
--   Finite Instrument: tensor Power born Weight coordinate sum eq
-- statement:
--   For an arbitrary, possibly correlated tensor-power input, summing every
--   observed history except one selected coordinate gives exactly the base
--   instrument's Born mass on that coordinate's true reduced density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L342-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L342-L428

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_coordinate_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      (∑ history : tensorPowerHistory Omega attempts,
        if tensorPowerHistoryAt Omega attempts history trial = outcome then
          (I.tensorPower attempts).bornWeight history rho
        else 0) =
        I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by sorry
