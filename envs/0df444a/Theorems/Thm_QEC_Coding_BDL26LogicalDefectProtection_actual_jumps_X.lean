-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_jumps_X
-- name    : QEC.Coding.BDL26LogicalDefectProtection.actual_jumps_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:35:50.061462+00:00
-- url     : https://prove2.me/theorems/2cca0431-4689-49e9-915c-2b4452adabc4
-- title:
--   BDL26 Logical Defect Protection: actual jumps X
-- statement:
--   Actual same-H coherent grouped-frequency jumps consume derived XYZ protection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L514-L522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L514-L522

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

theorem QEC.Coding.BDL26LogicalDefectProtection.actual_jumps_X
    (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ) :
    JumpProtected (BDL26BoundedRateDavies.jump S (n+2) rate)
      (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) := by sorry
