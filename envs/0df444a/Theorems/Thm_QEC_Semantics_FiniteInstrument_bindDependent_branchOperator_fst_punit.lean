-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_branchOperator_fst_punit
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_branchOperator_fst_punit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:03.751055+00:00
-- url     : https://prove2.me/theorems/38219e5f-df14-47f3-ba61-d3719b75dfb7
-- title:
--   Finite Instrument: bind Dependent branch Operator fst punit
-- statement:
--   If the first instrument has only the unit observation, retaining a
--   second-stage outcome applies that second observed branch to the complete
--   first-stage Kraus map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L284-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L284-L300

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.bindDependent_branchOperator_fst_punit
    (I : FiniteInstrument κ PUnit H K)
    (J : FiniteInstrument κ' Ω K L) (outcome : Ω) (A : Operator H) :
    (I.bindDependent (fun _ => J)).branchOperator
        ⟨PUnit.unit, outcome⟩ A =
      J.branchOperator outcome (I.kraus.inducedMap A) := by sorry
