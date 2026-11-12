-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_raw_invalid
-- name    : QEC.Coding.BDL26LogicalDefectProtection.raw_invalid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:46:28.378632+00:00
-- url     : https://prove2.me/theorems/1aac1b82-ba85-41da-bcab-30876dffb423
-- title:
--   BDL26 Logical Defect Protection: raw invalid
-- statement:
--   Unrealisable raw labels contribute zero, with no false converse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L289-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L289-L295

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

theorem QEC.Coding.BDL26LogicalDefectProtection.raw_invalid (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (E : Binary (Physical S (n+2))) (O : BDL26PairedDecoderChannel.Op S n) :
    (toHermitianQubitOperator E * O - O * toHermitianQubitOperator E) * projector S (n+2) w = 0 := by sorry
