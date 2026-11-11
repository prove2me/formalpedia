-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_trace_Y
-- name    : QEC.Coding.BDL26PairedDecoderChannel.readout_trace_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:23:23.870522+00:00
-- url     : https://prove2.me/theorems/d06f11ec-4c02-4edb-a803-653d983dfae2
-- title:
--   BDL26 Paired Decoder Channel: readout trace Y
-- statement:
--   The BDL26 Paired Decoder Channel construction uses the readout trace Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L461-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L461-L467

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

theorem QEC.Coding.BDL26PairedDecoderChannel.readout_trace_Y (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * Qubit.pauliY) =
      LinearMap.trace ℂ (Register S n) (A * dressedY S n) := by sorry
