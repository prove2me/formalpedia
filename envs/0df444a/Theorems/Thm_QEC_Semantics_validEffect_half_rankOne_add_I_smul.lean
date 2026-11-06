-- Prove2me | Theorems.Thm_QEC_Semantics_validEffect_half_rankOne_add_I_smul
-- name    : QEC.Semantics.validEffect_half_rankOne_add_I_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:59.136529+00:00
-- url     : https://prove2.me/theorems/19f5c8eb-d202-4f8f-9cde-d6d2297dc27a
-- title:
--   Semantics: valid Effect half rank One add I smul
-- statement:
--   The equal-weight projector onto a phase-shifted pair of basis vectors is an effect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L105-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L105-L117

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v

theorem QEC.Semantics.validEffect_half_rankOne_add_I_smul {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    {i j : κ} (hij : i ≠ j) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
        (b i + Complex.I • b j)).toLinearMap) := by sorry
