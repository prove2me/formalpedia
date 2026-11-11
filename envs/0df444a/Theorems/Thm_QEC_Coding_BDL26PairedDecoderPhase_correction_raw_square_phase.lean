-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_correction_raw_square_phase
-- name    : QEC.Coding.BDL26PairedDecoderPhase.correction_raw_square_phase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:28:03.422418+00:00
-- url     : https://prove2.me/theorems/b4340300-f030-4df4-a51b-95ffbdab522f
-- title:
--   BDL26 Paired Decoder Phase: correction raw square phase
-- statement:
--   The canonical before-correction overlap is retained without assuming it vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L414-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L414-L417

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

theorem QEC.Coding.BDL26PairedDecoderPhase.correction_raw_square_phase (s : Visible S n) :
    (binaryMul (correction S n s) (correction S n s)).phase =
      ∑ q, xCorrection S n s.1 q * zCorrection S n s.2 q := by sorry
