-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_logical_Y_protected
-- name    : QEC.Coding.BDL26LogicalDefectProtection.logical_Y_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:51:02.469399+00:00
-- url     : https://prove2.me/theorems/50342bdd-fbfc-4f44-b04f-ace714893a74
-- title:
--   BDL26 Logical Defect Protection: logical Y protected
-- statement:
--   Logical Y follows from logical invariance; no physical-error invariance is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L501-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L501-L511

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

theorem QEC.Coding.BDL26LogicalDefectProtection.logical_Y_protected (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedY S n -
      BDL26PairedDecoderChannel.dressedY S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        protectedProjector S n = 0 := by sorry
