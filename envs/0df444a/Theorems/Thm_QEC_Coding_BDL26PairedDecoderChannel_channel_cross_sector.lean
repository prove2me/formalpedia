-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_channel_cross_sector
-- name    : QEC.Coding.BDL26PairedDecoderChannel.channel_cross_sector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:42:05.629225+00:00
-- url     : https://prove2.me/theorems/90655ca4-bfdf-436d-8931-ae57be3479f3
-- title:
--   BDL26 Paired Decoder Channel: channel cross sector
-- statement:
--   Distinct original syndrome coherences are removed by the measurement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L134-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L134-L148

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_28
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_29

theorem QEC.Coding.BDL26PairedDecoderChannel.channel_cross_sector (s t : Visible S n) (hst : s ≠ t) (A : Op S n) :
    channel S n (atom S n s * A * atom S n t) = 0 := by sorry
