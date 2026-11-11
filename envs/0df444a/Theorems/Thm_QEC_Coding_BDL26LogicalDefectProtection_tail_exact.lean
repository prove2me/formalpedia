-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_tail_exact
-- name    : QEC.Coding.BDL26LogicalDefectProtection.tail_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:36:48.619066+00:00
-- url     : https://prove2.me/theorems/47583418-5fe4-47b0-bac8-1eece21c30a0
-- title:
--   BDL26 Logical Defect Protection: tail exact
-- statement:
--   The BDL26 Logical Defect Protection construction uses the tail exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L567-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L567-L574

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_exact

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

theorem QEC.Coding.BDL26LogicalDefectProtection.tail_exact (beta : ℝ) :
    clbtGibbsTailMass (protectedProjector S n) (gibbs S (n+2) beta) =
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) +
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) -
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) *
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) := by sorry
