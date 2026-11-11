-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_even_bounded_rate_application
-- name    : QEC.Coding.BDL26BoundedRateDavies.even_bounded_rate_application
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:43:52.321112+00:00
-- url     : https://prove2.me/theorems/98039011-05ba-4908-bc49-988197017666
-- title:
--   BDL26 Bounded Rate Davies: even bounded rate application
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the even bounded rate application property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L166-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L166-L175

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.even_bounded_rate_application (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S (2*k) ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S (2*k) rate (BDL26CSSHamiltonian.gibbs S (2*k) β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S (2*k) rate) ≤
        6 * Fintype.card (Physical S (2*k)) * hmax := by sorry
