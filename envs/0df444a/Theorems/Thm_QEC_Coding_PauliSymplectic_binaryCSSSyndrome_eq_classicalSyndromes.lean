-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_eq_classicalSyndromes
-- name    : QEC.Coding.PauliSymplectic.binaryCSSSyndrome_eq_classicalSyndromes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:17:52.4982+00:00
-- url     : https://prove2.me/theorems/dea4e25e-d943-4ad5-863b-b1efda44de6d
-- title:
--   Pauli Symplectic: binary CSSSyndrome eq classical Syndromes
-- statement:
--   The syndrome of the oriented binary CSS generator family is the tagged pair of
--   classical `P` and `Q` syndromes. The orthogonality assumption keeps the theorem
--   in the source-valid CSS setting, while the equality itself is algebraic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L27-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Syndrome.lean#L27-L65

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.PauliSymplectic.binaryCSSSyndrome_eq_classicalSyndromes
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E =
      Sum.elim (P E.vector.xPart) (Q E.vector.zPart) := by sorry
