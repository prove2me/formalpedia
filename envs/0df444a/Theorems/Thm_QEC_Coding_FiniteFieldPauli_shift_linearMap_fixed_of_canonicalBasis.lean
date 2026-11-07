-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_linearMap_fixed_of_canonicalBasis
-- name    : QEC.Coding.FiniteFieldPauli.shift_linearMap_fixed_of_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:46:12.847126+00:00
-- url     : https://prove2.me/theorems/71e3fff0-90ae-42fe-a67e-b0dced813125
-- title:
--   Finite Field Pauli: shift linear Map fixed of canonical Basis
-- statement:
--   Fixing every scalar multiple of the images of coordinate basis vectors
--   implies fixedness under the whole image of a finite-dimensional word map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L297-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L297-L314

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

theorem QEC.Coding.FiniteFieldPauli.shift_linearMap_fixed_of_canonicalBasis
    {κ : Type*} [Fintype κ]
    (L : Word F κ →ₗ[F] Word F ι) (ψ : Register F ι)
    (hfixed : ∀ (k : κ) (a : F),
      shift (L (a • canonicalBasisWord k)) ψ = ψ)
    (y : Word F κ) :
    shift (L y) ψ = ψ := by sorry
