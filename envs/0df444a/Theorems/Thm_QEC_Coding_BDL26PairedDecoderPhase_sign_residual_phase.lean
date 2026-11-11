-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sign_residual_phase
-- name    : QEC.Coding.BDL26PairedDecoderPhase.sign_residual_phase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:30:41.881273+00:00
-- url     : https://prove2.me/theorems/1d42a3d3-c032-44d2-a7a0-0b705d3fa94c
-- title:
--   BDL26 Paired Decoder Phase: sign residual phase
-- statement:
--   The phase shift is preserved even though the residual vectors agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L434-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L434-L439

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

theorem QEC.Coding.BDL26PairedDecoderPhase.sign_residual_phase (phase : ZMod 2) (s : Visible S n)
    (E : Binary (Physical S (n + 2))) :
    (residual S n s (binaryMul (binarySign phase) E)).phase =
      phase + (residual S n s E).phase := by sorry
