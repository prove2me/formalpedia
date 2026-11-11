-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_tail_union_bound
-- name    : QEC.Coding.BDL26LogicalDefectProtection.tail_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:37:08.305516+00:00
-- url     : https://prove2.me/theorems/a3ef3196-887d-43d0-9c30-e5b12187b74c
-- title:
--   BDL26 Logical Defect Protection: tail union bound
-- statement:
--   The BDL26 Logical Defect Protection construction uses the tail union bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L576-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L576-L581

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_union_bound

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

theorem QEC.Coding.BDL26LogicalDefectProtection.tail_union_bound (beta : ℝ) :
    clbtGibbsTailMass (protectedProjector S n) (gibbs S (n+2) beta) ≤
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) +
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) := by sorry
