-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_couplingIndex_card
-- name    : QEC.Coding.BDL26BoundedRateDavies.couplingIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:31:20.738786+00:00
-- url     : https://prove2.me/theorems/ceca337f-70da-41f3-b45e-14f5bbf4dfbf
-- title:
--   BDL26 Bounded Rate Davies: coupling Index card
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the coupling Index card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L58-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L58-L60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.couplingIndex_card : Fintype.card (CouplingIndex S n) =
    3 * Fintype.card (Physical S n) := by sorry
