-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_good_iff_residuals
-- name    : QEC.Coding.BDL26LogicalDefectProtection.good_iff_residuals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:29:26.449433+00:00
-- url     : https://prove2.me/theorems/211027f3-cacb-45c8-ad2b-0e682428e45a
-- title:
--   BDL26 Logical Defect Protection: good iff residuals
-- statement:
--   The BDL26 Logical Defect Protection construction uses the good iff residuals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L371-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L371-L389

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

theorem QEC.Coding.BDL26LogicalDefectProtection.good_iff_residuals (s : Visible S n) :
    s ∈ good S n ↔ ∀ q axis,
      (code S n).InGeneratedGroupUpToSign (residual S n s (CSSDaviesLocality.singlePauli q axis)) := by sorry
