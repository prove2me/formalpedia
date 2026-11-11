-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_h1Coordinate_eq_pairing
-- name    : QEC.Coding.BDL26LogicalDefectProtection.h1Coordinate_eq_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:16:54.0772+00:00
-- url     : https://prove2.me/theorems/be006471-1921-492e-8e71-efab352809a8
-- title:
--   BDL26 Logical Defect Protection: h1 Coordinate eq pairing
-- statement:
--   The actual rank-one coordinate is exactly pairing with the derived partner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L78-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L78-L85

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

theorem QEC.Coding.BDL26LogicalDefectProtection.h1Coordinate_eq_pairing (a : BDL26FiniteCohomology.Cocycle S (n+2)) :
    h1Coordinate S n a = wordPairing a.val (zWord S n) := by sorry
