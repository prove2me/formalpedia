-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_x_row_iff
-- name    : QEC.Coding.BDL26LogicalDefectProtection.x_row_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:26:01.517133+00:00
-- url     : https://prove2.me/theorems/68b5d22a-d179-430a-84b0-e5a8a591e9a9
-- title:
--   BDL26 Logical Defect Protection: x row iff
-- statement:
--   No boundary witness or rank certificate is supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L92-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L92-L104

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

theorem QEC.Coding.BDL26LogicalDefectProtection.x_row_iff (a : W S n) (ha : zSyndrome S (n+2) a = 0) :
    (∃ c, wordLinearMapTranspose (xSyndrome S (n+2)) c = a) ↔
      wordPairing a (zWord S n) = 0 := by sorry
