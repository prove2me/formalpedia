-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_z_check_card
-- name    : QEC.Coding.BDL26CSSHamiltonian.z_check_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:24:03.38663+00:00
-- url     : https://prove2.me/theorems/0bef9146-f18d-414b-b2c0-3baf53ef1cac
-- title:
--   BDL26 CSSHamiltonian: z check card
-- statement:
--   The BDL26 CSSHamiltonian construction uses the z check card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L21-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L21-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.z_check_card (z : ZLabel S n) : (checkSupport S n (.inl z)).card = zDegree (presentation S n) z := by sorry
