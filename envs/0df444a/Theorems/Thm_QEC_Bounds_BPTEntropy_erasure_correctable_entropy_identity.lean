-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_erasure_correctable_entropy_identity
-- name    : QEC.Bounds.BPTEntropy.erasure_correctable_entropy_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:29.728203+00:00
-- url     : https://prove2.me/theorems/e7b36256-dc2a-4e59-8875-b8227ce14522
-- title:
--   BPTEntropy: erasure correctable entropy identity
-- statement:
--   For every code-supported finite density operator, exact recovery from the
--   concrete qudit erasure channel gives the BPT correctable-region identity
--   `S(M | complement M) = -S(M)`, written without a conditional-entropy field.
--   The quantified state is arbitrary; its spectral purification is used only for
--   the #412 reference-decoupling bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L205-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L205-L265

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.erasure_correctable_entropy_identity
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho) :
    rho.vonNeumannEntropy -
        (S.erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by sorry
