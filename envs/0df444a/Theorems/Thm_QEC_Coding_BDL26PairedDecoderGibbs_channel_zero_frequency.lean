-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_zero_frequency
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.channel_zero_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:18:05.242198+00:00
-- url     : https://prove2.me/theorems/56b2bec9-d4a1-4a29-bab8-12c5e0da592f
-- title:
--   BDL26 Paired Decoder Gibbs: channel zero frequency
-- statement:
--   Complete frequency reconstruction retains exactly the zero-frequency image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L308-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L308-L324

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem QEC.Coding.BDL26PairedDecoderGibbs.channel_zero_frequency (A : Op S n) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A 0) = channel S n A := by sorry
