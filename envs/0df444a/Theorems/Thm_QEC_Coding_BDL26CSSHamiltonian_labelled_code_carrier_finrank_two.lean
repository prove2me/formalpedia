-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelled_code_carrier_finrank_two
-- name    : QEC.Coding.BDL26CSSHamiltonian.labelled_code_carrier_finrank_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:32:38.591192+00:00
-- url     : https://prove2.me/theorems/edcfb229-6734-476b-94ed-551cc028392d
-- title:
--   BDL26 CSSHamiltonian: labelled code carrier finrank two
-- statement:
--   The BDL26 CSSHamiltonian construction uses the labelled code carrier finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L49-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L49-L52

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

theorem QEC.Coding.BDL26CSSHamiltonian.labelled_code_carrier_finrank_two :
    Module.finrank ℂ (labelledCode S n).carrier = 2 := by sorry
