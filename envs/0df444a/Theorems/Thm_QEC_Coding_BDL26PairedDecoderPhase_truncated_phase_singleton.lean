-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_truncated_phase_singleton
-- name    : QEC.Coding.BDL26PairedDecoderPhase.truncated_phase_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:13:31.819082+00:00
-- url     : https://prove2.me/theorems/53d773e6-7682-4fd4-9044-8444770ee337
-- title:
--   BDL26 Paired Decoder Phase: truncated phase singleton
-- statement:
--   Truncating the phase to {s} at identity bare data gives only the single atom.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L557-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L557-L560

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

theorem QEC.Coding.BDL26PairedDecoderPhase.truncated_phase_singleton (s : Visible S n) :
    (∑ a ∈ ({s} : Finset (Visible S n)),
      commutationPhase (correction S n a) binaryOne • atom S n a) = atom S n s := by sorry
