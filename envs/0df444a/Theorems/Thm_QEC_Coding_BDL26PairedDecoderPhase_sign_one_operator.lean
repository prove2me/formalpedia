-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sign_one_operator
-- name    : QEC.Coding.BDL26PairedDecoderPhase.sign_one_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:39:46.4692+00:00
-- url     : https://prove2.me/theorems/3858977d-ecf2-4130-9fd8-8111222bef82
-- title:
--   BDL26 Paired Decoder Phase: sign one operator
-- statement:
--   Direct use of the registered signed Hermitian API, not general multiplicativity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L456-L459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L456-L459

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

theorem QEC.Coding.BDL26PairedDecoderPhase.sign_one_operator (E : Binary (Physical S (n + 2))) :
    toHermitianQubitOperator (binaryMul (binarySign 1) E) = -toHermitianQubitOperator E := by sorry
