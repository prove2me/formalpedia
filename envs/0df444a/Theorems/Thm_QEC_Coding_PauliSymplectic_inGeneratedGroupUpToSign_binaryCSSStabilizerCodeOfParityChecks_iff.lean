-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
-- name    : QEC.Coding.PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:14.251694+00:00
-- url     : https://prove2.me/theorems/9665453c-1ac3-48f5-ac1c-f34c289555f3
-- title:
--   Pauli Symplectic: in Generated Group Up To Sign binary CSSStabilizer Code Of Parity Checks iff
-- statement:
--   Generated-group membership up to the stored sign is exactly componentwise
--   membership in the Q-row/X and P-row/Z codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L108-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L108-L142

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

theorem QEC.Coding.PauliSymplectic.inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InGeneratedGroupUpToSign E ↔
      E.vector.xPart ∈ (parityCheckRowCode Q).carrier ∧
      E.vector.zPart ∈ (parityCheckRowCode P).carrier := by sorry
