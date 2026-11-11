-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_jump_eq_sqrt_smul
-- name    : QEC.Coding.BDL26CSSDaviesLocality.jump_eq_sqrt_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:24:40.614202+00:00
-- url     : https://prove2.me/theorems/cd716bf4-3d56-40f4-bfed-f308d1100cc1
-- title:
--   BDL26 CSSDavies Locality: jump eq sqrt smul
-- statement:
--   The BDL26 CSSDavies Locality construction uses the jump eq sqrt smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L158-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L158-L164

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

theorem QEC.Coding.BDL26CSSDaviesLocality.jump_eq_sqrt_smul (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) =
    (Real.sqrt (rate (q,a) ω) : ℂ) •
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val := by sorry
