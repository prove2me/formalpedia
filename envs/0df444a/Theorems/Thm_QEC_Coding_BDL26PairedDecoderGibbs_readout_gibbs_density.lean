-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_readout_gibbs_density
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.readout_gibbs_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:22:58.081352+00:00
-- url     : https://prove2.me/theorems/da3e13bc-1c0d-400e-a550-83db3ad74cc9
-- title:
--   BDL26 Paired Decoder Gibbs: readout gibbs density
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the readout gibbs density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L572-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L572-L575

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.readout_gibbs_density (beta : ℝ) :
    (readout S n).mapDensity (gibbs S (n+2) beta) = ThermalEncoding.PauliLikePair.maximallyMixedQubit := by sorry
