-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_inner
-- name    : QEC.Coding.BDL26BoundedRateDavies.coupling_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:25:29.26983+00:00
-- url     : https://prove2.me/theorems/1d318845-1fc3-4d88-a6b5-b19335d90083
-- title:
--   BDL26 Bounded Rate Davies: coupling inner
-- statement:
--   Every actual coupling preserves the physical register inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L23-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L23-L32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.coupling_inner (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (v w : Qubit.QubitRegister (Physical S n)) :
    inner ℂ (coupling S n q a v) (coupling S n q a w) = inner ℂ v w := by sorry
