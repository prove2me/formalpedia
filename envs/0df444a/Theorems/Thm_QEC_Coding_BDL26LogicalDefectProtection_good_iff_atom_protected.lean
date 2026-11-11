-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_good_iff_atom_protected
-- name    : QEC.Coding.BDL26LogicalDefectProtection.good_iff_atom_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:29:40.243647+00:00
-- url     : https://prove2.me/theorems/8383b87c-42dd-455c-89c9-54620a9a5824
-- title:
--   BDL26 Logical Defect Protection: good iff atom protected
-- statement:
--   Exact atom converse for the actual physical coupling family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L419-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L419-L431

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

theorem QEC.Coding.BDL26LogicalDefectProtection.good_iff_atom_protected (s : Visible S n) :
    s ∈ good S n ↔ ∀ q axis,
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 := by sorry
