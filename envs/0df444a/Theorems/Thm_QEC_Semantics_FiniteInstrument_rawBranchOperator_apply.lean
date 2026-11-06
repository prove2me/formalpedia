-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
-- name    : QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:44.377073+00:00
-- url     : https://prove2.me/theorems/969968f8-9795-4685-8e48-14f3ad0fcd77
-- title:
--   Finite Instrument: raw Branch Operator apply
-- statement:
--   The Finite Instrument construction uses the raw Branch Operator apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L35-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L35-L40

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
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

theorem QEC.Semantics.FiniteInstrument.rawBranchOperator_apply (I : FiniteInstrument κ Ω H K) (index : κ)
    (A : Operator H) :
    I.rawBranchOperator index A =
      (I.kraus.operator index).comp
        (A.comp (LinearMap.adjoint (I.kraus.operator index))) := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
