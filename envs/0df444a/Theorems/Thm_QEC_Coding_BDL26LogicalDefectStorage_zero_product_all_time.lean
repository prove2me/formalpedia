-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_zero_product_all_time
-- name    : QEC.Coding.BDL26LogicalDefectStorage.zero_product_all_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:16:39.665389+00:00
-- url     : https://prove2.me/theorems/c7fb3b28-05c8-49cf-94f1-585d4f084819
-- title:
--   BDL26 Logical Defect Storage: zero product all time
-- statement:
--   Includes g=0 and mu=0 without division or any positivity premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L396-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L396-L410

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

theorem QEC.Coding.BDL26LogicalDefectStorage.zero_product_all_time (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hz : g S n rate * mass S n beta = 0)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht = 0 ∧ decodedError S n rate beta eta t ht = 0 := by sorry
