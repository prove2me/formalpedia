-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_bounded_rate_application
-- name    : QEC.Coding.BDL26BoundedRateDavies.bounded_rate_application
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:26:48.373949+00:00
-- url     : https://prove2.me/theorems/1d66fdfd-f19a-4c25-8556-d278ed5d42e0
-- title:
--   BDL26 Bounded Rate Davies: bounded rate application
-- statement:
--   Physical positive bounded detailed-balance rates give both conclusions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L137-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L137-L148

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.bounded_rate_application
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (β hmax : ℝ) (_hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
        6 * Fintype.card (Physical S n) * hmax := by sorry
