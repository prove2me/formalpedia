-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_protected_Z_iff
-- name    : QEC.Coding.BDL26LogicalDefectProtection.protected_Z_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:12:44.976916+00:00
-- url     : https://prove2.me/theorems/fb87e39e-3a59-4000-89e0-245297362797
-- title:
--   BDL26 Logical Defect Protection: protected Z iff
-- statement:
--   The BDL26 Logical Defect Protection construction uses the protected Z iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L257-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L257-L262

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

theorem QEC.Coding.BDL26LogicalDefectProtection.protected_Z_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (toHermitianQubitOperator E * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * toHermitianQubitOperator E) * atom S n s = 0 ↔
        dX S n s E = 0 := by sorry
