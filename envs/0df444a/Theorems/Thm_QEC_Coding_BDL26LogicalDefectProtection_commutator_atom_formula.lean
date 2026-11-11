-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_commutator_atom_formula
-- name    : QEC.Coding.BDL26LogicalDefectProtection.commutator_atom_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:17:08.566789+00:00
-- url     : https://prove2.me/theorems/1817e13d-adee-49cc-a268-4f447572a0a9
-- title:
--   BDL26 Logical Defect Protection: commutator atom formula
-- statement:
--   Only Pauli exchange is used; normalized Hermitian realization is not multiplicative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L180-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L180-L199

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

theorem QEC.Coding.BDL26LogicalDefectProtection.commutator_atom_formula (s : Visible S n) (E L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    (toHermitianQubitOperator E * dressed S n L - dressed S n L * toHermitianQubitOperator E) *
      atom S n s = coefficient S n s E L •
        (toHermitianQubitOperator L * toHermitianQubitOperator E * atom S n s) := by sorry
