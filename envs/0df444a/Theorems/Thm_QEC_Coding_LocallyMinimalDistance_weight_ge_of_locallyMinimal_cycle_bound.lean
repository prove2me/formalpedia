-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_weight_ge_of_locallyMinimal_cycle_bound
-- name    : QEC.Coding.LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:30.377137+00:00
-- url     : https://prove2.me/theorems/e0f225dc-9a49-4f40-a6dd-0cd981452294
-- title:
--   Locally Minimal Distance: weight ge of locally Minimal cycle bound
-- statement:
--   A local-minimal cycle bound transfers to all nontrivial homology classes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L75-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L75-L85

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (lowerBound : Nat)
    (hlocal : ∀ c : C, c ∈ Z → c ≠ 0 →
      IsLocallyMinimal weight moves c → lowerBound ≤ weight c)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    lowerBound ≤ weight c := by sorry
