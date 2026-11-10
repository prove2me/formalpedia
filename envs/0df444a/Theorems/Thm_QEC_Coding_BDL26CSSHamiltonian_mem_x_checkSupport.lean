-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
-- name    : QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:57:55.467113+00:00
-- url     : https://prove2.me/theorems/8ed49de6-97da-47f4-b2b7-b376f78e6f4b
-- title:
--   BDL26 CSSHamiltonian: mem x check Support
-- statement:
--   The BDL26 CSSHamiltonian construction uses the mem x check Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L17-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean#L17-L19

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport (x : XLabel S n) (q : Physical S n) :
    q ∈ checkSupport S n (.inr x) ↔ (presentation S n).xq x q = true := by sorry
