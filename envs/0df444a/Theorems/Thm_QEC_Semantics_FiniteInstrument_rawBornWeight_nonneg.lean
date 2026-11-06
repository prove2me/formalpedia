-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_nonneg
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:26.973856+00:00
-- url     : https://prove2.me/theorems/0ca53902-318e-4dee-85dd-c4095cf5c2b7
-- title:
--   Finite Instrument: raw Born Weight nonneg
-- statement:
--   Raw Born weights are nonnegative because their literal branch operators are positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L66-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L66-L70

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

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_nonneg (I : FiniteInstrument κ Ω H K) (index : κ)
    (rho : DensityOperator H) :
    0 ≤ I.rawBornWeight index rho := by sorry
