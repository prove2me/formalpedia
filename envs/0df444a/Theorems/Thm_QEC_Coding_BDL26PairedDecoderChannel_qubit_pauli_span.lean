-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_qubit_pauli_span
-- name    : QEC.Coding.BDL26PairedDecoderChannel.qubit_pauli_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:16:23.867201+00:00
-- url     : https://prove2.me/theorems/c7c209cb-9137-46c7-820a-ade4f5a25387
-- title:
--   BDL26 Paired Decoder Channel: qubit pauli span
-- statement:
--   Complete complex Pauli spanning; no Hermitian-input restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L470-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L470-L486

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

theorem QEC.Coding.BDL26PairedDecoderChannel.qubit_pauli_span (A : Operator Qubit.QubitSpace) :
    ∃ a b c d : ℂ, A = a • (1 : Operator Qubit.QubitSpace) + b • Qubit.pauliX +
      c • Qubit.pauliY + d • Qubit.pauliZ := by sorry
