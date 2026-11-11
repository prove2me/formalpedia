-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_jumps_Z
-- name    : QEC.Coding.BDL26LogicalDefectProtection.actual_jumps_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:34:13.627428+00:00
-- url     : https://prove2.me/theorems/202d24b1-c15f-433a-8075-6ec7ca9ea612
-- title:
--   BDL26 Logical Defect Protection: actual jumps Z
-- statement:
--   The BDL26 Logical Defect Protection construction uses the actual jumps Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L524-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L524-L532

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

theorem QEC.Coding.BDL26LogicalDefectProtection.actual_jumps_Z
    (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ) :
    JumpProtected (BDL26BoundedRateDavies.jump S (n+2) rate)
      (BDL26PairedDecoderChannel.dressedZ S n) (protectedProjector S n) := by sorry
