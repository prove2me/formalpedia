-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_source_even_storage
-- name    : QEC.Coding.BDL26LogicalDefectStorage.source_even_storage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:41:34.15507+00:00
-- url     : https://prove2.me/theorems/9eb5a0c3-251b-472f-8b58-d85947d5fafb
-- title:
--   BDL26 Logical Defect Storage: source even storage
-- statement:
--   Every source-even level uses the same physical beta and rate cap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L511-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L511-L524

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

theorem QEC.Coding.BDL26LogicalDefectStorage.source_even_storage (rates : ∀ j, Rate S j) (beta hmax : ℝ)
    (hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ j qa omega, 0 < rates j qa omega ∧ rates j qa omega ≤ hmax)
    (hDB : ∀ j qa omega, rates j qa (BDL26BoundedRateDavies.oppositeFrequency S (j+2) omega) =
      Real.exp (-beta * omega.val) * rates j qa omega)
    (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j+2 = 2*k ∧ ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
      (encodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta) ∧
      (encodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta) := by sorry
