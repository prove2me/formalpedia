-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_code_carrier
-- name    : QEC.Coding.BDL26CSSHamiltonian.code_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:29:08.836415+00:00
-- url     : https://prove2.me/theorems/cbe136b5-f941-4e4b-a524-b2001af98c5a
-- title:
--   BDL26 CSSHamiltonian: code carrier
-- statement:
--   Equality of the actual semantic carriers, with no dimension assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L113-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L113-L119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.code_carrier :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S n) (xSyndrome S n)
      (row_orthogonal S n)).code.carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier := by sorry
