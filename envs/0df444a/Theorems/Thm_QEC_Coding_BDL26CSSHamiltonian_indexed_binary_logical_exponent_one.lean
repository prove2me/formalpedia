-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_indexed_binary_logical_exponent_one
-- name    : QEC.Coding.BDL26CSSHamiltonian.indexed_binary_logical_exponent_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:31:50.560098+00:00
-- url     : https://prove2.me/theorems/57487a93-ca7b-4b8f-b789-393ae5c4fd02
-- title:
--   BDL26 CSSHamiltonian: indexed binary logical exponent one
-- statement:
--   The BDL26 CSSHamiltonian construction uses the indexed binary logical exponent one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L195-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L195-L198

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119

theorem QEC.Coding.BDL26CSSHamiltonian.indexed_binary_logical_exponent_one (depth : Nat) (i : LevelIndex depth) :
    Fintype.card (BDL26IndexedDecoder.FamilyQ S depth i) -
      CSSGibbs.checkRank (zSyndrome S i.val) - CSSGibbs.checkRank (xSyndrome S i.val) = 1 := by sorry
