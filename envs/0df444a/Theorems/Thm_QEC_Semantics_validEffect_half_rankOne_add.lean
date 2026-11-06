-- Prove2me | Theorems.Thm_QEC_Semantics_validEffect_half_rankOne_add
-- name    : QEC.Semantics.validEffect_half_rankOne_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:50.509685+00:00
-- url     : https://prove2.me/theorems/f50209e2-1b9d-4b65-bcd8-f58dd0e6453e
-- title:
--   Semantics: valid Effect half rank One add
-- statement:
--   The equal-weight projector onto the span of two distinct basis vectors is an effect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L91-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L91-L102

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

theorem QEC.Semantics.validEffect_half_rankOne_add {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    {i j : κ} (hij : i ≠ j) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap) := by sorry
