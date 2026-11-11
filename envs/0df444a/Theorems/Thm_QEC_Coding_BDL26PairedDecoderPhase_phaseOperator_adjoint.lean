-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_adjoint
-- name    : QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:13:45.814372+00:00
-- url     : https://prove2.me/theorems/07d7fe87-a6b0-4eb1-9620-9d421d2de1a6
-- title:
--   BDL26 Paired Decoder Phase: phase Operator adjoint
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the phase Operator adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L181-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L181-L189

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_adjoint


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

theorem QEC.Coding.BDL26PairedDecoderPhase.phaseOperator_adjoint (logical : Binary (Physical S (n + 2))) :
    LinearMap.adjoint (phaseOperator S n logical) = phaseOperator S n logical := by sorry
