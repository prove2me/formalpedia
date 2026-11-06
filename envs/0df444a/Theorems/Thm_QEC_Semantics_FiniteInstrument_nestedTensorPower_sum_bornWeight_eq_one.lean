-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_sum_bornWeight_eq_one
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorPower_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:59:31.661357+00:00
-- url     : https://prove2.me/theorems/5e1b809c-999b-4d84-ba87-33b3b1a87d48
-- title:
--   Finite Instrument: nested Tensor Power sum born Weight eq one
-- statement:
--   A complete nested tensor power has normalized total observable Born mass
--   for every density operator on its literal nested input carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L171-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean#L171-L177

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.nestedTensorPower_sum_bornWeight_eq_one
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    ∑ outcome, (nestedTensorPower I branches depth).bornWeight outcome rho = 1 := by sorry
