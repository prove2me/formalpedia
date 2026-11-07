-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:17:49.195474+00:00
-- url     : https://prove2.me/theorems/062372d3-7bac-49d3-8c61-72a200287c84
-- title:
--   Pauli Symplectic: binary CSSSyndrome equal XZ
-- statement:
--   Equal X/Z coordinates, the binary support representation of Y up to phase,
--   have the two classical syndromes `(P y, Q y)` for every binary phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L93-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L93-L103

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι) =
      Sum.elim (P y) (Q y) := by sorry
