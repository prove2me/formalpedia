-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_readout_encoding_density
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.readout_encoding_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:19:45.268262+00:00
-- url     : https://prove2.me/theorems/a7dd563e-996d-4528-9942-78c4f6bc1a11
-- title:
--   BDL26 Paired Decoder Gibbs: readout encoding density
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the readout encoding density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L447-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L447-L450

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.readout_encoding_density (beta : ℝ) (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((encoding S n beta).mapDensity rho) = rho := by sorry
