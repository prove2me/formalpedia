-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_rowSupport_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.rowSupport_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:33:17.746202+00:00
-- url     : https://prove2.me/theorems/14ed3518-1415-4ffd-956c-840ed3c59548
-- title:
--   BDL26 CSSDavies Locality: row Support eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the row Support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L31-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L31-L33

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

theorem QEC.Coding.BDL26CSSDaviesLocality.rowSupport_eq (j : Label S n) :
    CSSDaviesLocality.rowSupport (zSyndrome S n) (xSyndrome S n) j =
      checkSupport S n j := by sorry
