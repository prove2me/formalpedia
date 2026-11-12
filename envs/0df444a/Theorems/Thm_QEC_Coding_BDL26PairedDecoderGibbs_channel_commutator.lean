-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_commutator
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.channel_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:16:45.5772+00:00
-- url     : https://prove2.me/theorems/83eaa427-94f5-4820-91f8-23cd337fafc3
-- title:
--   BDL26 Paired Decoder Gibbs: channel commutator
-- statement:
--   This uses the input sector energies, not merely the output support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L277-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L277-L289

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem QEC.Coding.BDL26PairedDecoderGibbs.channel_commutator (A : Op S n) :
    channel S n (hamiltonian S (n+2) * A - A * hamiltonian S (n+2)) = 0 := by sorry
