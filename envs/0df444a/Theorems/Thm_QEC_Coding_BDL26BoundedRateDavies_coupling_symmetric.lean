-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_symmetric
-- name    : QEC.Coding.BDL26BoundedRateDavies.coupling_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:25:36.381437+00:00
-- url     : https://prove2.me/theorems/394decb2-7455-4333-b475-c77f6be4e209
-- title:
--   BDL26 Bounded Rate Davies: coupling symmetric
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the coupling symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L50-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L50-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.coupling_symmetric (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (coupling S n q a).IsSymmetric := by sorry
