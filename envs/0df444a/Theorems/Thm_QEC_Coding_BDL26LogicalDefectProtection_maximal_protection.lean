-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_maximal_protection
-- name    : QEC.Coding.BDL26LogicalDefectProtection.maximal_protection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:46:51.932134+00:00
-- url     : https://prove2.me/theorems/d285fbb3-fbbc-4973-8ad1-54cd3fbf314a
-- title:
--   BDL26 Logical Defect Protection: maximal protection
-- statement:
--   The BDL26 Logical Defect Protection construction uses the maximal protection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L492-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L492-L495

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

theorem QEC.Coding.BDL26LogicalDefectProtection.maximal_protection (A : Finset (Visible S n)) :
    Protects S n A ↔ BDL26TwoSectorBadProjector.selected S (n+2) A * protectedProjector S n =
      BDL26TwoSectorBadProjector.selected S (n+2) A := by sorry
