-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_hamiltonian_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.hamiltonian_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:36:06.219195+00:00
-- url     : https://prove2.me/theorems/1e64531a-0d34-428f-895c-252652d4d74c
-- title:
--   BDL26 CSSDavies Locality: hamiltonian eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the hamiltonian eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L49-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L49-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_hamiltonian_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.hamiltonian_eq :
    CSSDaviesLocality.hamiltonian (zSyndrome S n) (xSyndrome S n) =
      BDL26CSSHamiltonian.hamiltonian S n := by sorry
