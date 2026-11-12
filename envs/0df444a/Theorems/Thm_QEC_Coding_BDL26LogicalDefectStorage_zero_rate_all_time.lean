-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_zero_rate_all_time
-- name    : QEC.Coding.BDL26LogicalDefectStorage.zero_rate_all_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:44:12.64866+00:00
-- url     : https://prove2.me/theorems/a1298cb5-f955-4ec9-af49-6e39aef548c2
-- title:
--   BDL26 Logical Defect Storage: zero rate all time
-- statement:
--   The BDL26 Logical Defect Storage construction uses the zero rate all time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L591-L596
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L591-L596

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

theorem QEC.Coding.BDL26LogicalDefectStorage.zero_rate_all_time (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n (fun _ _ => 0) beta eta t ht = 0 ∧
    decodedError S n (fun _ _ => 0) beta eta t ht = 0 := by sorry
