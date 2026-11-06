-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_tensor
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:39.461862+00:00
-- url     : https://prove2.me/theorems/8fa1b6ba-b313-4444-955b-0c0f97c60a33
-- title:
--   Finite Instrument: raw Born Weight tensor
-- statement:
--   Literal raw Kraus masses factor over a tensor-product density input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L94-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L94-L112

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

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) (rho : DensityOperator H)
    (sigma : DensityOperator R) (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).rawBornWeight (leftIndex, rightIndex)
        (DensityOperator.tensorDensity rho sigma) =
      I.rawBornWeight leftIndex rho * J.rawBornWeight rightIndex sigma := by sorry
