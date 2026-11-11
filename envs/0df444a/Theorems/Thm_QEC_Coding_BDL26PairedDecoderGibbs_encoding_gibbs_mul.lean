-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_gibbs_mul
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.encoding_gibbs_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:09:40.002222+00:00
-- url     : https://prove2.me/theorems/4f2a4376-1317-46ff-aaf7-994c025b344e
-- title:
--   BDL26 Paired Decoder Gibbs: encoding gibbs mul
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the encoding gibbs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L493-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L493-L516

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.encoding_gibbs_mul (beta : ℝ) (A : Operator Qubit.QubitSpace) :
    encoding S n beta A = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * pairEmbedding (dressedPauliPair S n) A) := by sorry
