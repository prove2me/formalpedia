-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_Y_right
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.encoding_Y_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:21:15.598587+00:00
-- url     : https://prove2.me/theorems/40d8e6c7-a557-4b6e-97e1-8b568c7f3478
-- title:
--   BDL26 Paired Decoder Gibbs: encoding Y right
-- statement:
--   The BDL26 Paired Decoder Gibbs construction uses the encoding Y right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L553-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L553-L556

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

theorem QEC.Coding.BDL26PairedDecoderGibbs.encoding_Y_right (beta : ℝ) :
    encoding S n beta Qubit.pauliY = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedY S n) := by sorry
