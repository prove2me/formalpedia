-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_bornWeight_any_path_failure_le
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_any_path_failure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:00:07.559678+00:00
-- url     : https://prove2.me/theorems/6e463d8f-61fb-4758-a655-48aa085a1d5f
-- title:
--   Finite Instrument: nested Tensor Power born Weight any path failure le
-- statement:
--   A finite weighted union bound over all actual leaves of a nested tensor
--   power.  Each leaf is charged to its true marginal failure mass, so the nested
--   input may be arbitrarily correlated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBornMass.lean#L100-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBornMass.lean#L100-L169

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

theorem QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_any_path_failure_le
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    (∑ history ∈ Finset.univ.filter
        (fun history : nestedTensorHistory Omega branches depth =>
          ∃ path : nestedTensorPath branches depth,
            fails (nestedTensorHistoryAt Omega branches depth history path)),
      (nestedTensorPower I branches depth).bornWeight history rho) ≤
      ∑ path : nestedTensorPath branches depth,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by sorry
