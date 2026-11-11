-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_syndromeEnergy_eq
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.syndromeEnergy_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:17:28.809198+00:00
-- url     : https://prove2.me/theorems/6da8caa8-9855-4518-97eb-ff9f2839e0bc
-- title:
--   BDL26 Paired Decoder Gibbs: syndrome Energy eq
-- statement:
--   Literal labelled-check energy, with no rank substitution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L155-L159

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.syndromeEnergy_eq (s : Visible S n) :
    syndromeEnergy S n s = groundEnergy S n +
      2 * ((HammingWeight s.1.val : ℝ) + HammingWeight s.2.val) := by sorry
