-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_code_dimension_eq
-- name    : QEC.QLDPC.QuantumCodeFamily.code_dimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:59.639869+00:00
-- url     : https://prove2.me/theorems/6d09bd5a-366b-4094-ad01-cf2660ddd5e2
-- title:
--   Quantum Code Family: code dimension eq
-- statement:
--   Encoded dimension is certified by the actual indexed quantum-code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L65-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L65-L68

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.code_dimension_eq (F : QuantumCodeFamily A ι κ) (a : A) :
    (F.presentation a).code.dimension =
      (F.presentation a).alphabetSize ^ F.encodedDimension a := by sorry
