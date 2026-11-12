-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_encoder_reference_mul
-- name    : QEC.Coding.BDL26LogicalDefectStorage.encoder_reference_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:24:36.9273+00:00
-- url     : https://prove2.me/theorems/61671e84-3089-48be-8ab9-18df3800399b
-- title:
--   BDL26 Logical Defect Storage: encoder reference mul
-- statement:
--   The BDL26 Logical Defect Storage construction uses the encoder reference mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L205-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L205-L209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97

theorem QEC.Coding.BDL26LogicalDefectStorage.encoder_reference_mul (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encoder S n beta eta.toOperator = (reference S n beta).toOperator * observable S n eta := by sorry
