-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_ground_mul_hamiltonian
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.ground_mul_hamiltonian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:14:56.817529+00:00
-- url     : https://prove2.me/theorems/3c850975-db2b-4764-9514-d7fdcd68a4de
-- title:
--   BDL26 Paired Decoder Gibbs: ground mul hamiltonian
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the ground mul hamiltonian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L256-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L256-L262

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.ground_mul_hamiltonian :
    groundProjector S n * hamiltonian S (n+2) =
      (groundEnergy S n : ℂ) • groundProjector S n := by sorry
