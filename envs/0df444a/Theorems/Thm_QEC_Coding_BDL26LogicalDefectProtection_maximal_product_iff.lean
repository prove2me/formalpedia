-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_maximal_product_iff
-- name    : QEC.Coding.BDL26LogicalDefectProtection.maximal_product_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:31:26.985085+00:00
-- url     : https://prove2.me/theorems/3c1099a8-6547-4542-9a40-d0bb315009cf
-- title:
--   BDL26 Logical Defect Protection: maximal product iff
-- statement:
--   The BDL26 Logical Defect Protection construction uses the maximal product iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L478-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L478-L490

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

theorem QEC.Coding.BDL26LogicalDefectProtection.maximal_product_iff (A : Finset (Visible S n)) :
    BDL26TwoSectorBadProjector.selected S (n+2) A * protectedProjector S n =
      BDL26TwoSectorBadProjector.selected S (n+2) A ↔ A ⊆ good S n := by sorry
