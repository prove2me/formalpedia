-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_hamiltonian_mul_ground
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_ground
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:17:41.706013+00:00
-- url     : https://prove2.me/theorems/fb6e3936-1fe1-4d08-9df4-0aaaf1633e3a
-- title:
--   BDL26 Paired Decoder Gibbs: hamiltonian mul ground
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the hamiltonian mul ground property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L248-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L248-L254

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_ground :
    hamiltonian S (n+2) * groundProjector S n =
      (groundEnergy S n : ℂ) • groundProjector S n := by sorry
