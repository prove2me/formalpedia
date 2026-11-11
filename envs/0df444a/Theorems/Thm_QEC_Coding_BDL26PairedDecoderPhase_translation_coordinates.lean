-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_translation_coordinates
-- name    : QEC.Coding.BDL26PairedDecoderPhase.translation_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:22:08.593263+00:00
-- url     : https://prove2.me/theorems/d8f37fb9-962d-469e-9434-30176b85df8a
-- title:
--   BDL26 Paired Decoder Phase: translation coordinates
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the translation coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L54-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L54-L57

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

theorem QEC.Coding.BDL26PairedDecoderPhase.translation_coordinates (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    translation S n E s =
      (translateX S n s.1 E.vector.xPart, translateZ S n s.2 E.vector.zPart) := by sorry
