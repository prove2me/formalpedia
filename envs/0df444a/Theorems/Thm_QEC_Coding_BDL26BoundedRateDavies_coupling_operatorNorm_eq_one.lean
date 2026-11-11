-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_operatorNorm_eq_one
-- name    : QEC.Coding.BDL26BoundedRateDavies.coupling_operatorNorm_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:26:01.437198+00:00
-- url     : https://prove2.me/theorems/dc7b3621-f452-4a4c-b922-b3581d35016a
-- title:
--   BDL26 Bounded Rate Davies: coupling operator Norm eq one
-- statement:
--   Exact norm one is proved, never supplied as a bath assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L40-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L40-L45

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.coupling_operatorNorm_eq_one (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    operatorNorm (coupling S n q a) = 1 := by sorry
