-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
-- name    : QEC.Coding.PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:45.003579+00:00
-- url     : https://prove2.me/theorems/3e28d8c3-a40e-4d4b-bb2a-37b5cb5d7c1f
-- title:
--   Pauli Symplectic: in Binary Normalizer binary CSSStabilizer Code Of Parity Checks iff
-- statement:
--   Normalizer membership for the parity-check CSS code is exactly componentwise
--   membership in `ker P` and `ker Q`, preserving the P/Z and Q/X orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L45-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L45-L102

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_CSS_Distance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u v
open QEC.Coding.PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InBinaryNormalizer E ↔
      E.vector.xPart ∈ (parityCheckKernelCode P).carrier ∧
      E.vector.zPart ∈ (parityCheckKernelCode Q).carrier := by sorry
