-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_coefficient_Z_one
-- name    : QEC.Coding.BDL26LogicalDefectProtection.coefficient_Z_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:47:09.43803+00:00
-- url     : https://prove2.me/theorems/32c9a240-c3f2-4d51-af61-81c5d890abbd
-- title:
--   BDL26 Logical Defect Protection: coefficient Z one
-- statement:
--   A one-bit defect gives exactly -2 times the post-correction sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L272-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L272-L278

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

theorem QEC.Coding.BDL26LogicalDefectProtection.coefficient_Z_one (s : Visible S n) (E : Binary (Physical S (n+2)))
    (h : dX S n s E = 1) :
    coefficient S n s E (BDL26BareLogicalPair.logicalZ S (n+2)) =
      -2 * commutationPhase (correction S n (translation S n E s))
        (BDL26BareLogicalPair.logicalZ S (n+2)) := by sorry
