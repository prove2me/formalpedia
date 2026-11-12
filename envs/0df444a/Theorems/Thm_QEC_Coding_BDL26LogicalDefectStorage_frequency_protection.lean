-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_frequency_protection
-- name    : QEC.Coding.BDL26LogicalDefectStorage.frequency_protection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:41:47.74257+00:00
-- url     : https://prove2.me/theorems/40e22b40-9cea-4f3d-b567-6d06dec0930f
-- title:
--   BDL26 Logical Defect Storage: frequency protection
-- statement:
--   The BDL26 Logical Defect Storage construction uses the frequency protection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L536-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L536-L550

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97

theorem QEC.Coding.BDL26LogicalDefectStorage.frequency_protection (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).x -
      (logical S n).x * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 ∧
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).z -
      (logical S n).z * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 := by sorry
