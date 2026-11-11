-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_trace_duality
-- name    : QEC.Coding.BDL26PairedDecoderChannel.trace_duality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:15:43.564674+00:00
-- url     : https://prove2.me/theorems/ce01cfe7-2383-4a7e-abe5-eb91a1da7c8c
-- title:
--   BDL26 Paired Decoder Channel: trace duality
-- statement:
--   The constructed state and observable transforms are actual trace adjoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L123-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L123-L131

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

theorem QEC.Coding.BDL26PairedDecoderChannel.trace_duality (A O : Op S n) :
    LinearMap.trace ℂ (Register S n) (channel S n A * O) =
      LinearMap.trace ℂ (Register S n) (A * heisenberg S n O) := by sorry
