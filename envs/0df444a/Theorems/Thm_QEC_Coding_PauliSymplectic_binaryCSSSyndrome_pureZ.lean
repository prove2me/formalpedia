-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_pureZ
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_pureZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:43:44.46634+00:00
-- url     : https://prove2.me/theorems/16472f91-8fc9-4e7f-b953-adc61d252af8
-- title:
--   Pauli Symplectic: binary CSSSyndrome pure Z
-- statement:
--   A pure-Z error has zero `P` syndrome and classical `Q` syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L79-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L79-L87

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_pureZ
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (z : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (cssZCheck z) =
      Sum.elim (0 : Word (ZMod 2) κP) (Q z) := by sorry
