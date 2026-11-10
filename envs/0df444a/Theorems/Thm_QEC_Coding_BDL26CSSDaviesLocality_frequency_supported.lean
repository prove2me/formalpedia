-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
-- name    : QEC.Coding.BDL26CSSDaviesLocality.frequency_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:22:22.616685+00:00
-- url     : https://prove2.me/theorems/0e5c662f-dc46-4a2a-93cc-b0ac2af68498
-- title:
--   BDL26 CSSDavies Locality: frequency supported
-- statement:
--   All real frequencies, including those outside the actual Bohr spectrum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L136-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L136-L141

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.frequency_supported (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω) := by sorry
