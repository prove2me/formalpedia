-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_physical_storage
-- name    : QEC.Coding.BDL26LogicalDefectStorage.physical_storage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:32:25.46329+00:00
-- url     : https://prove2.me/theorems/0d97e8dd-bdbb-4fac-8e79-f705895ae804
-- title:
--   BDL26 Logical Defect Storage: physical storage
-- statement:
--   Physical beta and the original strictly positive bounded rate convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L362-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L362-L373

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

theorem QEC.Coding.BDL26LogicalDefectStorage.physical_storage (rate : Rate S n) (beta hmax : ℝ) (_hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ qa omega, 0 < rate qa omega ∧ rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    (encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta) ∧
    (encodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta) := by sorry
