-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_gibbs_eq_thermal_reference
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:06:44.704189+00:00
-- url     : https://prove2.me/theorems/442bbd1b-898b-4f3e-8608-761213615ffe
-- title:
--   BDL26 Paired Decoder Gibbs: gibbs eq thermal reference
-- statement:
--   The physical Gibbs density is the derived dressed thermal reference, for the SAME H.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L429-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L429-L437

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
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_416

theorem QEC.Coding.BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference (beta : ℝ) :
    gibbs S (n+2) beta = (dressedPauliPair S n).thermalReferenceState (auxiliaryGibbs S n beta) := by sorry
