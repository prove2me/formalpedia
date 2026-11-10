-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_jump_eq_sqrt_frequency
-- name    : QEC.Coding.BDL26BoundedRateDavies.jump_eq_sqrt_frequency
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:26:22.8986+00:00
-- url     : https://prove2.me/theorems/7cb2ef4f-255e-4dee-be3d-7621eaba3fd3
-- title:
--   BDL26 Bounded Rate Davies: jump eq sqrt frequency
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the jump eq sqrt frequency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L83-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.jump_eq_sqrt_frequency
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S n) :
    jump S n rate ((q,a),ω) = (Real.sqrt (rate (q,a) ω) : ℂ) •
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val := by sorry
