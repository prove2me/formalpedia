-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_x_check_card
-- name    : QEC.Coding.BDL26CSSHamiltonian.x_check_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:23:45.525427+00:00
-- url     : https://prove2.me/theorems/8f1627a7-5a87-42da-b0de-70b1211d5d52
-- title:
--   BDL26 CSSHamiltonian: x check card
-- statement:
--   The BDL26 CSSHamiltonian construction uses the x check card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L26-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L26-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.x_check_card (x : XLabel S n) : (checkSupport S n (.inr x)).card = xDegree (presentation S n) x := by sorry
