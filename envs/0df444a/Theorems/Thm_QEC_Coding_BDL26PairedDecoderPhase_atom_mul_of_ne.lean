-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_mul_of_ne
-- name    : QEC.Coding.BDL26PairedDecoderPhase.atom_mul_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:18:34.704609+00:00
-- url     : https://prove2.me/theorems/a0860dbb-9eef-43d0-a0f7-7e7db7bd4b89
-- title:
--   BDL26 Paired Decoder Phase: atom mul of ne
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the atom mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L131-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L131-L134

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

theorem QEC.Coding.BDL26PairedDecoderPhase.atom_mul_of_ne (s t : Visible S n) (h : s ≠ t) :
    atom S n s * atom S n t = 0 := by sorry
