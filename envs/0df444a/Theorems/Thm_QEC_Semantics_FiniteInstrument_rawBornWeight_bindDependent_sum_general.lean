-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_bindDependent_sum_general
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_bindDependent_sum_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:18.589538+00:00
-- url     : https://prove2.me/theorems/53fe1c73-7f91-4241-a2ce-1b99db609d74
-- title:
--   Finite Instrument: raw Born Weight bind Dependent sum general
-- statement:
--   Summing a complete dependent successor over its actual raw Kraus fibre
--   preserves the predecessor raw branch mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L131-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L131-L154

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

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_bindDependent_sum_general
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument (kappaTwo outcome) (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : kappa) :
    (∑ secondIndex : kappaTwo (I.observe firstIndex),
      (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho) =
        I.rawBornWeight firstIndex rho := by sorry
