-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_card_le_seven
-- name    : QEC.Coding.BDL26CSSHamiltonian.check_card_le_seven
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:30:37.717108+00:00
-- url     : https://prove2.me/theorems/29cfc3b9-6844-4dac-b740-8d599cc7ebd0
-- title:
--   BDL26 CSSHamiltonian: check card le seven
-- statement:
--   The BDL26 CSSHamiltonian construction uses the check card le seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L31-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L31-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.check_card_le_seven (j : Sum (ZLabel S n) (XLabel S n)) : (checkSupport S n j).card ≤ 7 := by sorry
