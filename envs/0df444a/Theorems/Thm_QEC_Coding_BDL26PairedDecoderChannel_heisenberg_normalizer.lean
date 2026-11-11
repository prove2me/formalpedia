-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_heisenberg_normalizer
-- name    : QEC.Coding.BDL26PairedDecoderChannel.heisenberg_normalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:16:49.0473+00:00
-- url     : https://prove2.me/theorems/5c777753-ceaa-4112-a822-afbea5abfdc3
-- title:
--   BDL26 Paired Decoder Channel: heisenberg normalizer
-- statement:
--   Literal identification with the original full CLBT phase-sum observable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L210-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L210-L236

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

theorem QEC.Coding.BDL26PairedDecoderChannel.heisenberg_normalizer (L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    heisenberg S n (toHermitianQubitOperator L) = dressed S n L := by sorry
