-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_decoded_le_encoded
-- name    : QEC.Coding.BDL26LogicalDefectStorage.decoded_le_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:32:53.783961+00:00
-- url     : https://prove2.me/theorems/5208e99d-521b-4f7f-b62e-03d7a1dd30b7
-- title:
--   BDL26 Logical Defect Storage: decoded le encoded
-- statement:
--   Contract the same physical readout, using its actual left inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L308-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L308-L318

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

theorem QEC.Coding.BDL26LogicalDefectStorage.decoded_le_encoded (rate : Rate S n) (beta : ℝ)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    decodedError S n rate beta eta t ht ≤ encodedError S n rate beta eta t ht := by sorry
