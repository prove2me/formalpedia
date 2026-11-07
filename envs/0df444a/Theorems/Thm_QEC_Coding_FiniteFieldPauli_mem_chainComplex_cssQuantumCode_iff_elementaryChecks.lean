-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_mem_chainComplex_cssQuantumCode_iff_elementaryChecks
-- name    : QEC.Coding.FiniteFieldPauli.mem_chainComplex_cssQuantumCode_iff_elementaryChecks
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:52:22.835104+00:00
-- url     : https://prove2.me/theorems/3a88c290-20b3-47f6-b48a-c0546144c5bd
-- title:
--   Finite Field Pauli: mem chain Complex css Quantum Code iff elementary Checks
-- statement:
--   For a finite chain complex it is enough to impose the scalar multiples of
--   individual boundary rows. These finite elementary X/Z checks have exactly the
--   same common fixed space as all words in the two CSS check codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L409-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L409-L443

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

theorem QEC.Coding.FiniteFieldPauli.mem_chainComplex_cssQuantumCode_iff_elementaryChecks
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode
      K.firstCoboundaryCheckCode K.middleBoundaryCode).carrier ↔
      (∀ (k : κ₀) (a : F),
        shift (wordLinearMapTranspose K.boundary1
          (a • canonicalBasisWord k)) ψ = ψ) ∧
      (∀ (k : κ₂) (a : F),
        phase (K.boundary2 (a • canonicalBasisWord k)) ψ = ψ) := by sorry
