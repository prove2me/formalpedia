-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_swap
-- name    : QEC.Coding.BDL26CSSHamiltonian.check_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:50:52.960209+00:00
-- url     : https://prove2.me/theorems/53e49fd5-94bb-41e1-9a81-171be0aaf6f0
-- title:
--   BDL26 CSSHamiltonian: check swap
-- statement:
--   The BDL26 CSSHamiltonian construction uses the check swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L98-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L98-L110

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

theorem QEC.Coding.BDL26CSSHamiltonian.check_swap (j : Sum (ZLabel S n) (XLabel S n)) :
    check S n j = QLDPC.chainComplexCSSRowCheck (complex S n) j.swap := by sorry
