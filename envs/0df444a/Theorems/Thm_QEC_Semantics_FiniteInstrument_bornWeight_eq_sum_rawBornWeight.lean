-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_eq_sum_rawBornWeight
-- name    : QEC.Semantics.FiniteInstrument.bornWeight_eq_sum_rawBornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:50.835704+00:00
-- url     : https://prove2.me/theorems/b5d41258-1a21-4ac3-ac66-1acfeba33a0e
-- title:
--   Finite Instrument: born Weight eq sum raw Born Weight
-- statement:
--   An observed Born weight is exactly the finite regrouping of its raw branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L73-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L73-L83

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

theorem QEC.Semantics.FiniteInstrument.bornWeight_eq_sum_rawBornWeight (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H) :
    I.bornWeight outcome rho =
      ∑ index : κ, if I.observe index = outcome then I.rawBornWeight index rho else 0 := by sorry
