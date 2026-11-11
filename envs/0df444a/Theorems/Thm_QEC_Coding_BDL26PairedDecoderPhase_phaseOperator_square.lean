-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_square
-- name    : QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:18:43.511226+00:00
-- url     : https://prove2.me/theorems/5902cb2b-d4db-405c-a470-2509bed16d24
-- title:
--   BDL26 Paired Decoder Phase: phase Operator square
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the phase Operator square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L172-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L172-L179

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_square
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_square


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

theorem QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_square (logical : Binary (Physical S (n + 2))) :
    phaseOperator S n logical * phaseOperator S n logical = 1 := by sorry
