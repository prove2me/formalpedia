-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sign_residual_vector
-- name    : QEC.Coding.BDL26PairedDecoderPhase.sign_residual_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:27:49.764573+00:00
-- url     : https://prove2.me/theorems/55ded035-4cf4-471a-af14-726c35d983be
-- title:
--   BDL26 Paired Decoder Phase: sign residual vector
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the sign residual vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L427-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L427-L431

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

theorem QEC.Coding.BDL26PairedDecoderPhase.sign_residual_vector (phase : ZMod 2) (s : Visible S n)
    (E : Binary (Physical S (n + 2))) :
    (residual S n s (binaryMul (binarySign phase) E)).vector = (residual S n s E).vector := by sorry
