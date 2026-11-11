-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_encode
-- name    : QEC.Coding.BDL26PairedDecoderChannel.readout_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:15:47.839982+00:00
-- url     : https://prove2.me/theorems/60a48e03-a2c5-4ec2-8f1b-88c44e1a70d9
-- title:
--   BDL26 Paired Decoder Channel: readout encode
-- statement:
--   The BDL26 Paired Decoder Channel construction uses the readout encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L569-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L569-L573

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

theorem QEC.Coding.BDL26PairedDecoderChannel.readout_encode (sigma : DensityOperator (dressedPauliPair S n).AuxiliarySpace)
    (A : Operator Qubit.QubitSpace) :
    readout S n ((dressedPauliPair S n).thermalEncoding sigma A) = A := by sorry
