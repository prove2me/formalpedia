-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_hamiltonian_mul_atom
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:06:53.701325+00:00
-- url     : https://prove2.me/theorems/8df246f7-bab7-4792-b8bd-5ff142dd0651
-- title:
--   BDL26 Paired Decoder Gibbs: hamiltonian mul atom
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the hamiltonian mul atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L161-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L161-L163

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_atom (s : Visible S n) :
    hamiltonian S (n+2) * atom S n s = (syndromeEnergy S n s : ℂ) • atom S n s := by sorry
