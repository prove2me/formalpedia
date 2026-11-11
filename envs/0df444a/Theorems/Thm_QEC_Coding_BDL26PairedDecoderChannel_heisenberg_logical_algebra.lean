-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_heisenberg_logical_algebra
-- name    : QEC.Coding.BDL26PairedDecoderChannel.heisenberg_logical_algebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:24:49.784568+00:00
-- url     : https://prove2.me/theorems/fb69ece4-7f0a-4674-aee2-b1ab42a3e2ea
-- title:
--   BDL26 Paired Decoder Channel: heisenberg logical algebra
-- statement:
--   The complete logical-algebra diagram follows from actual channel trace duality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L544-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L544-L560

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

theorem QEC.Coding.BDL26PairedDecoderChannel.heisenberg_logical_algebra (O : Operator Qubit.QubitSpace) :
    heisenberg S n (pairEmbedding (barePauliPair S n) O) =
      pairEmbedding (dressedPauliPair S n) O := by sorry
