-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_trace_rawBranchOperator_eq_rawBornWeight
-- name    : QEC.Semantics.FiniteInstrument.trace_rawBranchOperator_eq_rawBornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:40.855879+00:00
-- url     : https://prove2.me/theorems/03cab3c2-be1c-44ba-a007-32e3c7370f50
-- title:
--   Finite Instrument: trace raw Branch Operator eq raw Born Weight
-- statement:
--   Positivity makes each raw branch trace the corresponding real mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L55-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L55-L63

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

theorem QEC.Semantics.FiniteInstrument.trace_rawBranchOperator_eq_rawBornWeight
    (I : FiniteInstrument κ Ω H K) (index : κ) (rho : DensityOperator H) :
    LinearMap.trace Complex K (I.rawBranchOperator index rho.toOperator) =
      (I.rawBornWeight index rho : Complex) := by sorry
