-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_qubit_trace_ext
-- name    : QEC.Coding.BDL26PairedDecoderChannel.qubit_trace_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:25:06.275043+00:00
-- url     : https://prove2.me/theorems/2ba277e4-7154-4fb7-933f-09b883a4bfe9
-- title:
--   BDL26 Paired Decoder Channel: qubit trace ext
-- statement:
--   Four complex moments separate arbitrary qubit operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L489-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L489-L502

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

theorem QEC.Coding.BDL26PairedDecoderChannel.qubit_trace_ext (A B : Operator Qubit.QubitSpace)
    (hI : LinearMap.trace ℂ _ (A * 1) = LinearMap.trace ℂ _ (B * 1))
    (hX : LinearMap.trace ℂ _ (A * Qubit.pauliX) = LinearMap.trace ℂ _ (B * Qubit.pauliX))
    (hY : LinearMap.trace ℂ _ (A * Qubit.pauliY) = LinearMap.trace ℂ _ (B * Qubit.pauliY))
    (hZ : LinearMap.trace ℂ _ (A * Qubit.pauliZ) = LinearMap.trace ℂ _ (B * Qubit.pauliZ)) : A = B := by sorry
