-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_region_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.region_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:34:40.807397+00:00
-- url     : https://prove2.me/theorems/41b75e80-31f0-4da8-ac37-92aeb476db02
-- title:
--   BDL26 CSSDavies Locality: region eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the region eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L39-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L39-L40

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

theorem QEC.Coding.BDL26CSSDaviesLocality.region_eq (q : Physical S n) :
    CSSDaviesLocality.region (zSyndrome S n) (xSyndrome S n) q = region S n q := by sorry
