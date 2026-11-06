-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_bornWeight_path_failure_sum_eq
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_path_failure_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:22.561878+00:00
-- url     : https://prove2.me/theorems/f6211471-2613-4a88-8a12-7d7b86d0aebb
-- title:
--   Finite Instrument: nested Tensor Power born Weight path failure sum eq
-- statement:
--   Summing every nested history off one selected path gives exactly the
--   base-instrument failure mass on that path's true marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBornMass.lean#L47-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBornMass.lean#L47-L95

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_path_failure_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails] (branches : Nat) :
    ∀ (depth : Nat)
      (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (∑ history ∈ Finset.univ.filter
          (fun history : nestedTensorHistory Omega branches depth =>
            fails (nestedTensorHistoryAt Omega branches depth history path)),
        (nestedTensorPower I branches depth).bornWeight history rho) =
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by sorry
