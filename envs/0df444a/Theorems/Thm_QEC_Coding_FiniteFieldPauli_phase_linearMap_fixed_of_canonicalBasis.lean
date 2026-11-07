-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_linearMap_fixed_of_canonicalBasis
-- name    : QEC.Coding.FiniteFieldPauli.phase_linearMap_fixed_of_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:14.886871+00:00
-- url     : https://prove2.me/theorems/81c244d6-7647-43eb-bcf3-8dbf7ba237b6
-- title:
--   Finite Field Pauli: phase linear Map fixed of canonical Basis
-- statement:
--   Phase analogue of `shift_linearMap_fixed_of_canonicalBasis`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L317-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L317-L334

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

theorem QEC.Coding.FiniteFieldPauli.phase_linearMap_fixed_of_canonicalBasis
    {κ : Type*} [Fintype κ]
    (L : Word F κ →ₗ[F] Word F ι) (ψ : Register F ι)
    (hfixed : ∀ (k : κ) (a : F),
      phase (L (a • canonicalBasisWord k)) ψ = ψ)
    (y : Word F κ) :
    phase (L y) ψ = ψ := by sorry
