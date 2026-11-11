-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_mul_phaseOperator
-- name    : QEC.Coding.BDL26PairedDecoderPhase.atom_mul_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:28:37.087102+00:00
-- url     : https://prove2.me/theorems/5cc78685-88f4-4cba-a6ac-d8cef87b67d9
-- title:
--   BDL26 Paired Decoder Phase: atom mul phase Operator
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the atom mul phase Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L162-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L162-L170

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

theorem QEC.Coding.BDL26PairedDecoderPhase.atom_mul_phaseOperator (logical : Binary (Physical S (n + 2))) (s : Visible S n) :
    atom S n s * phaseOperator S n logical =
      commutationPhase (correction S n s) logical • atom S n s := by sorry
