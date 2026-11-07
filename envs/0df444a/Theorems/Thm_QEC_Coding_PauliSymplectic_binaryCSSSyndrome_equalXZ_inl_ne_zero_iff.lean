-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ_inl_ne_zero_iff
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_inl_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:27.390792+00:00
-- url     : https://prove2.me/theorems/8ac93389-df18-4398-97b8-819ea639a960
-- title:
--   Pauli Symplectic: binary CSSSyndrome equal XZ inl ne zero iff
-- statement:
--   The P-row component of an equal-X/Z syndrome is nonzero exactly when `P y` is.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L106-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L106-L116

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_inl_ne_zero_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    (fun p => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
      ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)
      (Sum.inl p)) ≠ 0 ↔ P y ≠ 0 := by sorry
