-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_indexedLabelledCode_carrier
-- name    : QEC.Coding.BDL26CSSHamiltonian.indexedLabelledCode_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:31:16.386577+00:00
-- url     : https://prove2.me/theorems/776f6211-7c15-49bd-a8d8-733a98362ee9
-- title:
--   BDL26 CSSHamiltonian: indexed Labelled Code carrier
-- statement:
--   The BDL26 CSSHamiltonian construction uses the indexed Labelled Code carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L183-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L183-L186

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

theorem QEC.Coding.BDL26CSSHamiltonian.indexedLabelledCode_carrier (depth : Nat) (i : LevelIndex depth) :
    (indexedLabelledCode S depth i).carrier =
      ((indexedFamily S depth).complex i).binaryCSSCode.stabilizer.code.carrier := by sorry
