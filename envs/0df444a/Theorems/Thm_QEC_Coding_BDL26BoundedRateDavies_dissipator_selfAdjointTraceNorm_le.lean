-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_dissipator_selfAdjointTraceNorm_le
-- name    : QEC.Coding.BDL26BoundedRateDavies.dissipator_selfAdjointTraceNorm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:24:27.894081+00:00
-- url     : https://prove2.me/theorems/e6dc06ad-604d-47e1-bf21-fa776dc8d31a
-- title:
--   BDL26 Bounded Rate Davies: dissipator self Adjoint Trace Norm le
-- statement:
--   The bound counts three physical couplings per qubit, with no gap multiplier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L120-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L120-L134

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.dissipator_selfAdjointTraceNorm_le
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ qa ω, 0 ≤ rate qa ω) (hu : ∀ qa ω, rate qa ω ≤ hmax) :
    selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
      6 * Fintype.card (Physical S n) * hmax := by sorry
