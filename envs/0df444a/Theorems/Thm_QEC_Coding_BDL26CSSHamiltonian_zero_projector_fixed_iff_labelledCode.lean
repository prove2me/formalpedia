-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_fixed_iff_labelledCode
-- name    : QEC.Coding.BDL26CSSHamiltonian.zero_projector_fixed_iff_labelledCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:29:48.871199+00:00
-- url     : https://prove2.me/theorems/1f7bc87b-5c6f-4a75-8e43-f1903337f170
-- title:
--   BDL26 CSSHamiltonian: zero projector fixed iff labelled Code
-- statement:
--   The BDL26 CSSHamiltonian construction uses the zero projector fixed iff labelled Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L100-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L100-L103

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

theorem QEC.Coding.BDL26CSSHamiltonian.zero_projector_fixed_iff_labelledCode (v : Qubit.QubitRegister (Physical S n)) :
    projector S n 0 v = v ↔ v ∈ (labelledCode S n).carrier := by sorry
