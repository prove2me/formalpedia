-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply_rankOne
-- name    : QEC.Semantics.ThermalEncoding.prepareRight_apply_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:07.578134+00:00
-- url     : https://prove2.me/theorems/0249ba7b-118b-4e95-beec-904fcce4d6fa
-- title:
--   Thermal Encoding: prepare Right apply rank One
-- statement:
--   The Thermal Encoding construction uses the prepare Right apply rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L809-L824
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L809-L824

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.ThermalEncoding.prepareRight_apply_rankOne (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (h g : H) :
    prepareRight H K sigma (InnerProductSpace.rankOne Complex h g).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (h ⊗ₜ[Complex] spectralEnsembleVector sigma i)
        (g ⊗ₜ[Complex] spectralEnsembleVector sigma i)).toLinearMap := by sorry
