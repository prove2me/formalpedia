-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_z_boundary_iff
-- name    : QEC.Coding.BDL26LogicalDefectProtection.residual_z_boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:25:21.682203+00:00
-- url     : https://prove2.me/theorems/7eb3e63f-6641-415b-afa9-672408c28990
-- title:
--   BDL26 Logical Defect Protection: residual z boundary iff
-- statement:
--   The BDL26 Logical Defect Protection construction uses the residual z boundary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L142-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L142-L145

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

theorem QEC.Coding.BDL26LogicalDefectProtection.residual_z_boundary_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (∃ c, wordLinearMapTranspose (zSyndrome S (n+2)) c =
      (residual S n s E).vector.zPart) ↔ dZ S n s E = 0 := by sorry
