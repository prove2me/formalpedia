-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_commute_hamiltonian
-- name    : QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:40:40.63623+00:00
-- url     : https://prove2.me/theorems/f2022a99-6acf-41f1-89c3-72242c3f57b6
-- title:
--   BDL26 Paired Decoder Phase: phase Operator commute hamiltonian
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the phase Operator commute hamiltonian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L249-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L249-L254

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

theorem QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_commute_hamiltonian (logical : Binary (Physical S (n + 2))) :
    Commute (phaseOperator S n logical) (hamiltonian S (n + 2)) := by sorry
