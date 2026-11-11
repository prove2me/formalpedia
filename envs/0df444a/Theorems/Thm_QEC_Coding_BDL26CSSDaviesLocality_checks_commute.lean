-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_checks_commute
-- name    : QEC.Coding.BDL26CSSDaviesLocality.checks_commute
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:37:29.835708+00:00
-- url     : https://prove2.me/theorems/5cd2ae72-078f-4555-b6b8-72b2e42893ad
-- title:
--   BDL26 CSSDavies Locality: checks commute
-- statement:
--   The BDL26 CSSDavies Locality construction uses the checks commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L66-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L66-L68

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

theorem QEC.Coding.BDL26CSSDaviesLocality.checks_commute (j k : Label S n) :
    Commute (toQubitOperator (check S n j)) (toQubitOperator (check S n k)) := by sorry
