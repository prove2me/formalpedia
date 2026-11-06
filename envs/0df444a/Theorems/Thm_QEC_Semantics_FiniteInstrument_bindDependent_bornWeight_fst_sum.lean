-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_bornWeight_fst_sum
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_bornWeight_fst_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:56.185966+00:00
-- url     : https://prove2.me/theorems/ba08fda8-60c7-43da-b873-98cfd8696588
-- title:
--   Finite Instrument: bind Dependent born Weight fst sum
-- statement:
--   Summing every observed successor outcome above a fixed predecessor
--   outcome recovers exactly that predecessor's Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L158-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean#L158-L196

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

theorem QEC.Semantics.FiniteInstrument.bindDependent_bornWeight_fst_sum
    (I : FiniteInstrument kappa Omega H K)
    (J : (outcome : Omega) -> FiniteInstrument (kappaTwo outcome) (Xi outcome) K L)
    (hJ : forall outcome, (J outcome).kraus.Complete)
    (outcome : Omega) (rho : DensityOperator H) :
    (∑ secondOutcome : Xi outcome,
      (I.bindDependent J).bornWeight ⟨outcome, secondOutcome⟩ rho) =
        I.bornWeight outcome rho := by sorry
