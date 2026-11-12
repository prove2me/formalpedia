-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_rowOperator_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.rowOperator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:31:29.30647+00:00
-- url     : https://prove2.me/theorems/318c6ca0-52ba-4355-abc4-93693bd5f466
-- title:
--   BDL26 CSSDavies Locality: row Operator eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the row Operator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L27-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L27-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.rowOperator_eq (j : Label S n) :
    CSSDaviesLocality.rowOperator (zSyndrome S n) (xSyndrome S n) j =
      toQubitOperator (check S n j) := by sorry
