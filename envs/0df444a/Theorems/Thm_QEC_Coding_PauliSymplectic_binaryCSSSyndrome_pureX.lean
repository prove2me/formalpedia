-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_pureX
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_pureX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:43:48.694877+00:00
-- url     : https://prove2.me/theorems/3e62008f-b8dc-48a2-a585-402e7239191f
-- title:
--   Pauli Symplectic: binary CSSSyndrome pure X
-- statement:
--   A pure-X error has classical `P` syndrome and zero `Q` syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L68-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L68-L76

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_pureX
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (x : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (cssXCheck x) =
      Sum.elim (P x) (0 : Word (ZMod 2) κQ) := by sorry
