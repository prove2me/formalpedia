-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_protected_empty
-- name    : QEC.Coding.BDL26PairedDecoderPhase.protected_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:53:01.398216+00:00
-- url     : https://prove2.me/theorems/62279c7c-0be0-421b-9ff7-c3c6e7d63409
-- title:
--   BDL26 Paired Decoder Phase: protected empty
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the protected empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L325-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L325-L328

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

theorem QEC.Coding.BDL26PairedDecoderPhase.protected_empty (E logical : Binary (Physical S (n + 2))) :
    (toHermitianQubitOperator E * dressed S n logical - dressed S n logical * toHermitianQubitOperator E) *
      BDL26TwoSectorBadProjector.selected S (n + 2) ∅ = 0 := by sorry
