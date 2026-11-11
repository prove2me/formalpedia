-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_reference
-- name    : QEC.Coding.BDL26PairedDecoderChannel.readout_reference
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:41:48.188755+00:00
-- url     : https://prove2.me/theorems/c1f5c6f1-2ed7-4a8c-a455-6a4076e25efb
-- title:
--   BDL26 Paired Decoder Channel: readout reference
-- statement:
--   Exact finite reference amplification of the complete operator identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L582-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L582-L585

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

theorem QEC.Coding.BDL26PairedDecoderChannel.readout_reference (r : Nat) (A : OperatorMatrix r (Register S n)) :
    OperatorMatrix.map (readout S n).toLinearMap A =
      OperatorMatrix.map (dressedPauliPair S n).thermalDecoding.toLinearMap A := by sorry
