-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_dissipator_eq_lindblad
-- name    : QEC.Coding.BDL26BoundedRateDavies.dissipator_eq_lindblad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:45:38.574509+00:00
-- url     : https://prove2.me/theorems/f3d825a6-b14a-4aab-bcaa-ea4502c9f62f
-- title:
--   BDL26 Bounded Rate Davies: dissipator eq lindblad
-- statement:
--   The BDL26 Bounded Rate Davies construction uses the dissipator eq lindblad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L96-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L96-L98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.dissipator_eq_lindblad
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    dissipator S n rate = lindbladDissipator (jump S n rate) := by sorry
