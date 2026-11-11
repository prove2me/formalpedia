-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_syndromeEnergy_ground_iff
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.syndromeEnergy_ground_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:07:46.339859+00:00
-- url     : https://prove2.me/theorems/24736326-25f8-4424-bf90-6a8cbf0af9a7
-- title:
--   BDL26 Paired Decoder Gibbs: syndrome Energy ground iff
-- statement:
--   Ground energy corresponds to the single zero word, not to energy zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L182-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L182-L197

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.syndromeEnergy_ground_iff (s : Visible S n) :
    syndromeEnergy S n s = groundEnergy S n ↔ s = zeroVisible S n := by sorry
