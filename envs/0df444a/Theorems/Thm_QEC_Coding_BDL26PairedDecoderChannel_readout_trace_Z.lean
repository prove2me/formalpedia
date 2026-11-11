-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_trace_Z
-- name    : QEC.Coding.BDL26PairedDecoderChannel.readout_trace_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:23:31.308343+00:00
-- url     : https://prove2.me/theorems/5b3dc934-b5a7-4331-8485-e61519c62167
-- title:
--   BDL26 Paired Decoder Channel: readout trace Z
-- statement:
--   The BDL26 Paired Decoder Channel construction uses the readout trace Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L453-L459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L453-L459

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

theorem QEC.Coding.BDL26PairedDecoderChannel.readout_trace_Z (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * Qubit.pauliZ) =
      LinearMap.trace ℂ (Register S n) (A * dressedZ S n) := by sorry
