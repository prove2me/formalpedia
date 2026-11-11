-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_truncated_not_protected
-- name    : QEC.Coding.BDL26PairedDecoderPhase.truncated_not_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:13:50.926206+00:00
-- url     : https://prove2.me/theorems/2a4c25b4-6abb-44e3-bc38-5e2a9f3f25ef
-- title:
--   BDL26 Paired Decoder Phase: truncated not protected
-- statement:
--   A nontrivial translation makes the truncated right-restricted commutator nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L563-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L563-L574

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

theorem QEC.Coding.BDL26PairedDecoderPhase.truncated_not_protected (s t : Visible S n) (hst : s ≠ t) :
    (toHermitianQubitOperator (bridgeError S n s t) * atom S n s -
      atom S n s * toHermitianQubitOperator (bridgeError S n s t)) * atom S n s ≠ 0 := by sorry
