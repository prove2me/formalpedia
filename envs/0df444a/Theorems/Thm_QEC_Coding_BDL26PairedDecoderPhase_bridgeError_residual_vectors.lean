-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_bridgeError_residual_vectors
-- name    : QEC.Coding.BDL26PairedDecoderPhase.bridgeError_residual_vectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:41:34.91502+00:00
-- url     : https://prove2.me/theorems/07539cb1-f032-42ad-b796-99677ed09119
-- title:
--   BDL26 Paired Decoder Phase: bridge Error residual vectors
-- statement:
--   Both computed residual vectors vanish; the residual sign is still unrestricted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L520-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L520-L534

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

theorem QEC.Coding.BDL26PairedDecoderPhase.bridgeError_residual_vectors (s t : Visible S n) :
    (residual S n s (bridgeError S n s t)).vector.xPart = 0 ∧
      (residual S n s (bridgeError S n s t)).vector.zPart = 0 := by sorry
