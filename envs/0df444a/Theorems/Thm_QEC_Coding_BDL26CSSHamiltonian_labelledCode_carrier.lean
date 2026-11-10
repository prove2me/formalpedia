-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelledCode_carrier
-- name    : QEC.Coding.BDL26CSSHamiltonian.labelledCode_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:30:35.038978+00:00
-- url     : https://prove2.me/theorems/8d97eb25-2e14-424b-b6f0-12a8af6836a6
-- title:
--   BDL26 CSSHamiltonian: labelled Code carrier
-- statement:
--   The BDL26 CSSHamiltonian construction uses the labelled Code carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L45-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L45-L47

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

theorem QEC.Coding.BDL26CSSHamiltonian.labelledCode_carrier :
    (labelledCode S n).carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier := by sorry
