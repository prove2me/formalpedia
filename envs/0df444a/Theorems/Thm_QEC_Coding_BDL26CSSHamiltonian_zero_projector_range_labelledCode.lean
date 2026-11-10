-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_range_labelledCode
-- name    : QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_labelledCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:37:55.884519+00:00
-- url     : https://prove2.me/theorems/2ccb7f16-dd1f-436e-a500-36b17fac76c1
-- title:
--   BDL26 CSSHamiltonian: zero projector range labelled Code
-- statement:
--   The BDL26 CSSHamiltonian construction uses the zero projector range labelled Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L90-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L90-L93

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

theorem QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_labelledCode :
    LinearMap.range (projector S n 0) = (labelledCode S n).carrier := by sorry
