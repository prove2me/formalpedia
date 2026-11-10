-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_sum_actualFrequency
-- name    : QEC.Coding.BDL26CSSDaviesLocality.sum_actualFrequency
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:24:39.900066+00:00
-- url     : https://prove2.me/theorems/48c69bbd-f27d-428a-b000-26d7322cc6ae
-- title:
--   BDL26 CSSDavies Locality: sum actual Frequency
-- statement:
--   Complete coherent reconstruction on the actual full-H spectrum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L190-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L190-L194

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.sum_actualFrequency (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (∑ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val) = coupling S n q a := by sorry
