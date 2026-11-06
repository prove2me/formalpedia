-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_bornWeight_any_coordinate_failure_le
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_any_coordinate_failure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:59:56.438795+00:00
-- url     : https://prove2.me/theorems/28638bd2-6303-494b-bd18-0c369bb68ff3
-- title:
--   Finite Instrument: tensor Power born Weight any coordinate failure le
-- statement:
--   A finite weighted union bound for tensor-power outcomes.  Failure of any
--   coordinate is charged to the sum of its true marginal failure masses; no
--   factorization or independence of the joint input is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L510-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L510-L573

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_any_coordinate_failure_le
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (attempts : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    (∑ history ∈ Finset.univ.filter (fun history : tensorPowerHistory Omega attempts =>
        ∃ trial : Fin attempts,
          fails (tensorPowerHistoryAt Omega attempts history trial)),
      (I.tensorPower attempts).bornWeight history rho) <=
      ∑ trial : Fin attempts,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by sorry
