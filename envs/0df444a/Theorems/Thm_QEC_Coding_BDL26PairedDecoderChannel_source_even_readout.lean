-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_source_even_readout
-- name    : QEC.Coding.BDL26PairedDecoderChannel.source_even_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:40:17.231204+00:00
-- url     : https://prove2.me/theorems/8fd34def-59d3-4442-8066-a89a1f445305
-- title:
--   BDL26 Paired Decoder Channel: source even readout
-- statement:
--   All original source-even levels in the existing C2-inclusive domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L588-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L588-L591

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

theorem QEC.Coding.BDL26PairedDecoderChannel.source_even_readout (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, n+2 = 2*k ∧ readout S n = (dressedPauliPair S n).thermalDecoding := by sorry
