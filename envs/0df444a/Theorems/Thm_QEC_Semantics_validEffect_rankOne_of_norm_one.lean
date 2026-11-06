-- Prove2me | Theorems.Thm_QEC_Semantics_validEffect_rankOne_of_norm_one
-- name    : QEC.Semantics.validEffect_rankOne_of_norm_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:13.871803+00:00
-- url     : https://prove2.me/theorems/ac0bcb7f-dceb-44c2-b045-e4b507c9bd0f
-- title:
--   Semantics: valid Effect rank One of norm one
-- statement:
--   A rank-one projector onto a unit vector is a valid effect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L29-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L29-L45

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

theorem QEC.Semantics.validEffect_rankOne_of_norm_one {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {x : H} (hx : ‖x‖ = 1) :
    ValidEffect (InnerProductSpace.rankOne Complex x x).toLinearMap := by sorry
