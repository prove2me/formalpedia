-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_hamiltonian_eq
-- name    : QEC.Coding.BDL26CSSHamiltonian.hamiltonian_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:29:08.373263+00:00
-- url     : https://prove2.me/theorems/84230a6a-833d-482f-8791-e1f32eceb08b
-- title:
--   BDL26 CSSHamiltonian: hamiltonian eq
-- statement:
--   The BDL26 CSSHamiltonian construction uses the hamiltonian eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L14-L14
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L14-L14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.hamiltonian_eq : hamiltonian S n = CSSGibbs.hamiltonian (zSyndrome S n) (xSyndrome S n) := by sorry
