-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_registerUnitary_apply_eq_finiteAlphabet
-- name    : QEC.Coding.FiniteFieldPauli.registerUnitary_apply_eq_finiteAlphabet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:34.302275+00:00
-- url     : https://prove2.me/theorems/7e9fb0d6-9c22-449c-88f5-61c279e9fa84
-- title:
--   Finite Field Pauli: register Unitary apply eq finite Alphabet
-- statement:
--   Both finite-field label relabellings act identically on register vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1590-L1594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1590-L1594

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.FiniteFieldPauli.registerUnitary_apply_eq_finiteAlphabet {ι' : Type u} [Fintype ι']
    [DecidableEq ι'] (ψ : Register F ι') :
    registerUnitary (F := F) ψ =
      Semantics.FiniteAlphabet.registerUnitary F ι' ψ := by sorry
