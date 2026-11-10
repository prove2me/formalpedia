-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
-- name    : QEC.Coding.BDL26CSSHamiltonian.check_hermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:54:11.551071+00:00
-- url     : https://prove2.me/theorems/eed70cfd-38c2-40c1-82c3-8e184a2252f7
-- title:
--   BDL26 CSSHamiltonian: check hermitian
-- statement:
--   The BDL26 CSSHamiltonian construction uses the check hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L121-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L121-L123

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

theorem QEC.Coding.BDL26CSSHamiltonian.check_hermitian (j : Sum (ZLabel S n) (XLabel S n)) :
    toHermitianQubitOperator (check S n j) = toQubitOperator (check S n j) := by sorry
