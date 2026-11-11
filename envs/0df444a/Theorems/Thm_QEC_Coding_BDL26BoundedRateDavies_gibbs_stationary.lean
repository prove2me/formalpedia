-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_gibbs_stationary
-- name    : QEC.Coding.BDL26BoundedRateDavies.gibbs_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:24:15.160339+00:00
-- url     : https://prove2.me/theorems/b4f3078a-c236-453d-b100-6ef7465ab1d4
-- title:
--   BDL26 Bounded Rate Davies: gibbs stationary
-- statement:
--   Detailed balance fixes the actual family Gibbs state, at the physical β.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L108-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L108-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.gibbs_stationary
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (β : ℝ)
    (hn : ∀ qa ω, 0 ≤ rate qa ω)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 := by sorry
