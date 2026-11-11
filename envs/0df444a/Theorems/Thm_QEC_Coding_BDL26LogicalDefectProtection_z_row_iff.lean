-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_z_row_iff
-- name    : QEC.Coding.BDL26LogicalDefectProtection.z_row_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:28:30.029049+00:00
-- url     : https://prove2.me/theorems/3ce14f3e-4480-4e09-a829-b4e84cb97a61
-- title:
--   BDL26 Logical Defect Protection: z row iff
-- statement:
--   The dual boundary classification follows from actual normal form and finite duality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L107-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L107-L129

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

theorem QEC.Coding.BDL26LogicalDefectProtection.z_row_iff (b : W S n) (hb : xSyndrome S (n+2) b = 0) :
    (∃ c, wordLinearMapTranspose (zSyndrome S (n+2)) c = b) ↔
      wordPairing (xWord S n) b = 0 := by sorry
