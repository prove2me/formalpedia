-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported_card
-- name    : QEC.Coding.BDL26CSSDaviesLocality.frequency_supported_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:40:48.789603+00:00
-- url     : https://prove2.me/theorems/cbe440c5-9059-41ad-b92a-17766b726f4e
-- title:
--   BDL26 CSSDavies Locality: frequency supported card
-- statement:
--   The BDL26 CSSDavies Locality construction uses the frequency supported card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L175-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L175-L179

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

theorem QEC.Coding.BDL26CSSDaviesLocality.frequency_supported_card (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω) ∧ (subsystem S n q).selected.card ≤ 50 := by sorry
