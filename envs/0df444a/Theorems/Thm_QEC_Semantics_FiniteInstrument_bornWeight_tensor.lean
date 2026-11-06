-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_tensor
-- name    : QEC.Semantics.FiniteInstrument.bornWeight_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:26.276143+00:00
-- url     : https://prove2.me/theorems/f963a4f3-ab85-4eb8-a8cc-1c11d812114e
-- title:
--   Finite Instrument: born Weight tensor
-- statement:
--   An observed tensor-product Born weight factors into the two observed
--   Born weights by regrouping its literal raw tensor branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L116-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L116-L150

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
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.bornWeight_tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) (rho : DensityOperator H)
    (sigma : DensityOperator R) (leftOutcome : Ω) (rightOutcome : Ω') :
    (I.tensor J).bornWeight (leftOutcome, rightOutcome)
        (DensityOperator.tensorDensity rho sigma) =
      I.bornWeight leftOutcome rho * J.bornWeight rightOutcome sigma := by sorry
