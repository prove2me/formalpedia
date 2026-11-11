-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_visible_eq_decoder_domains
-- name    : QEC.Coding.BDL26PairedDecoderPhase.visible_eq_decoder_domains
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:48:14.509924+00:00
-- url     : https://prove2.me/theorems/0accfc64-350f-4c27-a1d3-e1e786b90211
-- title:
--   BDL26 Paired Decoder Phase: visible eq decoder domains
-- statement:
--   The decoder's carrier is definitionally the visible carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L35-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L35-L36

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

theorem QEC.Coding.BDL26PairedDecoderPhase.visible_eq_decoder_domains :
    Visible S n = (XSyndromeDomain S n × ZSyndromeDomain S n) := by sorry
