-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_hamiltonian_commute_atom
-- name    : QEC.Coding.BDL26PairedDecoderPhase.hamiltonian_commute_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:37:35.326326+00:00
-- url     : https://prove2.me/theorems/1d315695-6f3e-495d-9d8e-3c6586e57770
-- title:
--   BDL26 Paired Decoder Phase: hamiltonian commute atom
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the hamiltonian commute atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L241-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L241-L247

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

theorem QEC.Coding.BDL26PairedDecoderPhase.hamiltonian_commute_atom (s : Visible S n) :
    Commute (hamiltonian S (n + 2)) (atom S n s) := by sorry
