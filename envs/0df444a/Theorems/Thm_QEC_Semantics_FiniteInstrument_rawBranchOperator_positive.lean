-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_positive
-- name    : QEC.Semantics.FiniteInstrument.rawBranchOperator_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:19.28226+00:00
-- url     : https://prove2.me/theorems/6b6e3558-688c-4cdf-b2b2-d82f1d7ff8cb
-- title:
--   Finite Instrument: raw Branch Operator positive
-- statement:
--   Literal raw Kraus branches preserve positivity of their input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L43-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L43-L47

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

theorem QEC.Semantics.FiniteInstrument.rawBranchOperator_positive (I : FiniteInstrument κ Ω H K) (index : κ)
    {A : Operator H} (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (I.rawBranchOperator index A) := by sorry
