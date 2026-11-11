-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_exists_nonzero_actualFrequency
-- name    : QEC.Coding.BDL26CSSDaviesLocality.exists_nonzero_actualFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:40:11.449675+00:00
-- url     : https://prove2.me/theorems/9cb3e48c-6563-4951-80ef-e7f2232bf64e
-- title:
--   BDL26 CSSDavies Locality: exists nonzero actual Frequency
-- statement:
--   A genuine component survives for every actual physical coupling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L197-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L197-L207

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

theorem QEC.Coding.BDL26CSSDaviesLocality.exists_nonzero_actualFrequency (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    ∃ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val ≠ 0 := by sorry
