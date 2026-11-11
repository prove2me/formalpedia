-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_normalizer_commute_phaseOperator
-- name    : QEC.Coding.BDL26PairedDecoderPhase.normalizer_commute_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:26:35.048116+00:00
-- url     : https://prove2.me/theorems/78164363-0cf2-4682-b67c-63c229109663
-- title:
--   BDL26 Paired Decoder Phase: normalizer commute phase Operator
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the normalizer commute phase Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L217-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L217-L223

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

theorem QEC.Coding.BDL26PairedDecoderPhase.normalizer_commute_phaseOperator (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    Commute (toHermitianQubitOperator logical) (phaseOperator S n logical) := by sorry
