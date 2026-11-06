-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_sum_bornWeight_eq_one
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:05.409598+00:00
-- url     : https://prove2.me/theorems/425d0d27-ae66-4896-869e-270b9561ddcf
-- title:
--   Finite Instrument: tensor Power sum born Weight eq one
-- statement:
--   Complete homogeneous tensor powers have normalized total observable Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L431-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/Composition.lean#L431-L435

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.tensorPower_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (hI : I.kraus.Complete) (n : Nat)
    (rho : DensityOperator (tensorPowerCarrier H n)) :
    ∑ outcome, (I.tensorPower n).bornWeight outcome rho = 1 := by sorry
