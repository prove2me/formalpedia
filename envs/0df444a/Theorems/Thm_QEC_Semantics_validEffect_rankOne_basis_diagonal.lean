-- Prove2me | Theorems.Thm_QEC_Semantics_validEffect_rankOne_basis_diagonal
-- name    : QEC.Semantics.validEffect_rankOne_basis_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:48.909194+00:00
-- url     : https://prove2.me/theorems/b5d9da75-45ef-4c9a-a4b7-f481a5f59989
-- title:
--   Semantics: valid Effect rank One basis diagonal
-- statement:
--   A matrix unit on a basis diagonal is a valid effect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L48-L52

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

theorem QEC.Semantics.validEffect_rankOne_basis_diagonal {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H) (i : κ) :
    ValidEffect (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by sorry
