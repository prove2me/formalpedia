-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_single_x
-- name    : QEC.Coding.BDL26LogicalDefectProtection.residual_single_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:22:33.656031+00:00
-- url     : https://prove2.me/theorems/884428d4-0699-4d8c-9aa2-e7207c158149
-- title:
--   BDL26 Logical Defect Protection: residual single x
-- statement:
--   The BDL26 Logical Defect Protection construction uses the residual single x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L319-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L319-L326

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

theorem QEC.Coding.BDL26LogicalDefectProtection.residual_single_x (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.zPart = 0 := by sorry
