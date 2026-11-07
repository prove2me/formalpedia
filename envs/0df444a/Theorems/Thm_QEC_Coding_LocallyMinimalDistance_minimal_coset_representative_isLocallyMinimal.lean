-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_minimal_coset_representative_isLocallyMinimal
-- name    : QEC.Coding.LocallyMinimalDistance.minimal_coset_representative_isLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:56.326194+00:00
-- url     : https://prove2.me/theorems/210832c6-93b7-486e-a425-e68d7caef07e
-- title:
--   Locally Minimal Distance: minimal coset representative is Locally Minimal
-- statement:
--   A minimum-weight coset representative is locally minimal under boundary moves.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L41-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L41-L51

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.minimal_coset_representative_isLocallyMinimal
    (weight : C → Nat) (B : AddSubgroup C) (moves : Finset C)
    (hmoves : ∀ m ∈ moves, m ∈ B) (c b : C) (hb : b ∈ B)
    (hmin : weight (c + b) = cosetWeight weight B c) :
    IsLocallyMinimal weight moves (c + b) := by sorry
