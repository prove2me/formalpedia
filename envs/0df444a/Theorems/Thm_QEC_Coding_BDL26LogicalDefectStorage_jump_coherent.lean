-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_jump_coherent
-- name    : QEC.Coding.BDL26LogicalDefectStorage.jump_coherent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:41:44.291408+00:00
-- url     : https://prove2.me/theorems/1da1b35d-a5a2-4d14-9729-d1c1629bab50
-- title:
--   BDL26 Logical Defect Storage: jump coherent
-- statement:
--   The actual coherent full-gap operator, keeping both copies of every degeneracy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L528-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L528-L534

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

theorem QEC.Coding.BDL26LogicalDefectStorage.jump_coherent (rate : Rate S n) (q : Physical S (n+2))
    (axis : CSSDaviesLocality.Axis) (omega : BDL26CSSDaviesLocality.Frequency S (n+2)) :
    jumps S n rate ((q,axis),omega) = (Real.sqrt (rate (q,axis) omega) : ℂ) •
      Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
        (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega.val := by sorry
