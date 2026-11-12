-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_gibbs_density
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.channel_gibbs_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:17:51.449761+00:00
-- url     : https://prove2.me/theorems/1aff39b5-16c5-4311-a34c-f9ab6eac1db9
-- title:
--   BDL26 Paired Decoder Gibbs: channel gibbs density
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the channel gibbs density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L390-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L390-L393

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.channel_gibbs_density (beta : ℝ) :
    (channel S n).mapDensity (gibbs S (n+2) beta) = groundDensity S n := by sorry
