-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
-- name    : QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:58:13.338254+00:00
-- url     : https://prove2.me/theorems/a5962064-4723-48f8-b72d-4ec09b12fc1a
-- title:
--   BDL26 CSSHamiltonian: mem z check Support
-- statement:
--   The BDL26 CSSHamiltonian construction uses the mem z check Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L13-L15
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L13-L15

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport (z : ZLabel S n) (q : Physical S n) :
    q ∈ checkSupport S n (.inl z) ↔ (presentation S n).qz q z = true := by sorry
