-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_left_inverse_density
-- name    : QEC.Coding.BDL26LogicalDefectStorage.left_inverse_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:22:01.848204+00:00
-- url     : https://prove2.me/theorems/d2f55184-2281-48db-8153-e67c58d680e1
-- title:
--   BDL26 Logical Defect Storage: left inverse density
-- statement:
--   The BDL26 Logical Defect Storage construction uses the left inverse density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L138-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L138-L140

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

theorem QEC.Coding.BDL26LogicalDefectStorage.left_inverse_density (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    (decoder S n).mapDensity ((encoder S n beta).mapDensity eta) = eta := by sorry
