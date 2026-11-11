-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_signed_bits
-- name    : QEC.Coding.BDL26LogicalDefectProtection.signed_bits
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:44:35.292986+00:00
-- url     : https://prove2.me/theorems/3d0a54a5-9a8a-438d-a096-621e2a66b401
-- title:
--   BDL26 Logical Defect Protection: signed bits
-- statement:
--   Negating the stored sign does not alter either logical bit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L169-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L169-L172

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24

theorem QEC.Coding.BDL26LogicalDefectProtection.signed_bits (phase : ZMod 2) (s : Visible S n) (E : Binary (Physical S (n+2))) :
    dX S n s (binaryMul (binarySign phase) E) = dX S n s E ∧
    dZ S n s (binaryMul (binarySign phase) E) = dZ S n s E := by sorry
