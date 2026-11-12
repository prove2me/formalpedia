-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_encode_density
-- name    : QEC.Coding.BDL26PairedDecoderChannel.readout_encode_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:42:12.644846+00:00
-- url     : https://prove2.me/theorems/1eb98490-d2e8-48cc-9053-3584dd3963b2
-- title:
--   BDL26 Paired Decoder Channel: readout encode density
-- statement:
--   The BDL26 Paired Decoder Channel construction uses the readout encode density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L575-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L575-L579

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

theorem QEC.Coding.BDL26PairedDecoderChannel.readout_encode_density (sigma : DensityOperator (dressedPauliPair S n).AuxiliarySpace)
    (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((dressedPauliPair S n).thermalEncoding sigma |>.mapDensity rho) = rho := by sorry
