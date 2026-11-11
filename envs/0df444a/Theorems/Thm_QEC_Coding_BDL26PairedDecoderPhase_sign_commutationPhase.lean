-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sign_commutationPhase
-- name    : QEC.Coding.BDL26PairedDecoderPhase.sign_commutationPhase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:29:44.981914+00:00
-- url     : https://prove2.me/theorems/10c8f44c-d8c8-447e-ac95-6413539648ed
-- title:
--   BDL26 Paired Decoder Phase: sign commutation Phase
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the sign commutation Phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L451-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L451-L453

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

theorem QEC.Coding.BDL26PairedDecoderPhase.sign_commutationPhase (phase : ZMod 2) (E logical : Binary (Physical S (n + 2))) :
    commutationPhase (binaryMul (binarySign phase) E) logical = commutationPhase E logical := by sorry
