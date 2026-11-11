-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_pauli_mul_atom
-- name    : QEC.Coding.BDL26PairedDecoderPhase.pauli_mul_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:22:31.672863+00:00
-- url     : https://prove2.me/theorems/48f4bc64-f591-4a07-b953-d50df2499b25
-- title:
--   BDL26 Paired Decoder Phase: pauli mul atom
-- statement:
--   Exact full-Pauli transport on the original atoms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L206-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L206-L209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_27
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_28

theorem QEC.Coding.BDL26PairedDecoderPhase.pauli_mul_atom (E : Binary (Physical S (n + 2))) (s : Visible S n) :
    toHermitianQubitOperator E * atom S n s =
      atom S n (translation S n E s) * toHermitianQubitOperator E := by sorry
