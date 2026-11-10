-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_oppositeFrequency_opposite
-- name    : QEC.Coding.BDL26BoundedRateDavies.oppositeFrequency_opposite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:24:05.648724+00:00
-- url     : https://prove2.me/theorems/3517c69c-4417-416e-a739-90da28fd1bfc
-- title:
--   BDL26 Bounded Rate Davies: opposite Frequency opposite
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the opposite Frequency opposite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L71-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.oppositeFrequency_opposite (ω : BDL26CSSDaviesLocality.Frequency S n) :
    oppositeFrequency S n (oppositeFrequency S n ω) = ω := by sorry
