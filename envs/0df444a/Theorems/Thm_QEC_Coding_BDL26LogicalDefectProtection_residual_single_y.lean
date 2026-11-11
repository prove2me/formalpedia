-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_single_y
-- name    : QEC.Coding.BDL26LogicalDefectProtection.residual_single_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:19:38.800196+00:00
-- url     : https://prove2.me/theorems/8fdca4d0-46d8-4bf8-bb12-c908ee3b8f31
-- title:
--   BDL26 Logical Defect Protection: residual single y
-- statement:
--   Direct same-residual Y proof, not multiplication of compressed commutators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L338-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L338-L343

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

theorem QEC.Coding.BDL26LogicalDefectProtection.residual_single_y (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.zPart = deltaZ S n s.2 q ∧
    BDL26CSSDaviesLocality.coupling S (n+2) q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) := by sorry
