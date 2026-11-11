-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_projector_properties
-- name    : QEC.Coding.BDL26LogicalDefectStorage.projector_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:09:19.885388+00:00
-- url     : https://prove2.me/theorems/d975c662-40c5-48c2-8c70-d9059736da34
-- title:
--   BDL26 Logical Defect Storage: projector properties
-- statement:
--   The BDL26 Logical Defect Storage construction uses the projector properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L155-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L155-L161

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

theorem QEC.Coding.BDL26LogicalDefectStorage.projector_properties : IsStarProjection (projector S n) ∧
    Commute (projector S n) (hamiltonian S (n+2)) ∧
    Commute (projector S n) (logical S n).x ∧ Commute (projector S n) (logical S n).z := by sorry
