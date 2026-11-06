-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_bind_sum_general
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_bind_sum_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:06.584787+00:00
-- url     : https://prove2.me/theorems/2115112d-503f-4208-8d97-efcc30b3788b
-- title:
--   Finite Instrument: raw Born Weight bind sum general
-- statement:
--   Summing a complete outcome-selected successor with a fixed raw index type
--   preserves the predecessor raw branch mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L37-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L37-L60

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Omega -> Type x} [forall outcome, Fintype (kappaTwo outcome)]
variable {Xi : Omega -> Type y} [forall outcome, Fintype (Xi outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
variable {kappaPrime : Type x} [Fintype kappaPrime]

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_bind_sum_general
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument kappaPrime (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : kappa) :
    (∑ secondIndex : kappaPrime,
      (I.bind J).rawBornWeight (firstIndex, secondIndex) rho) =
        I.rawBornWeight firstIndex rho := by sorry
