-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_nonzero_frequency
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.channel_nonzero_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:18:16.249595+00:00
-- url     : https://prove2.me/theorems/2996bdf8-2378-4f4e-8da2-4d905c5730f5
-- title:
--   BDL26 Paired Decoder Gibbs: channel nonzero frequency
-- statement:
--   Source-minus-target energy difference E' - E, with the original sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L292-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L292-L305

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.channel_nonzero_frequency (A : Op S n) (omega : ℝ) (h : omega ≠ 0) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A omega) = 0 := by sorry
