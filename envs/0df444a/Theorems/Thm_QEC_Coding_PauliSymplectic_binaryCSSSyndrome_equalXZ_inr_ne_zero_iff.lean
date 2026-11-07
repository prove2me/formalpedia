-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:34.974191+00:00
-- url     : https://prove2.me/theorems/2f596ecc-76ca-4190-a1e9-5539c47f3f1c
-- title:
--   Pauli Symplectic: binary CSSSyndrome equal XZ inr ne zero iff
-- statement:
--   The Q-row component of an equal-X/Z syndrome is nonzero exactly when `Q y` is.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L119-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L119-L129

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
      ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)
      (Sum.inr q)) ≠ 0 ↔ Q y ≠ 0 := by sorry
