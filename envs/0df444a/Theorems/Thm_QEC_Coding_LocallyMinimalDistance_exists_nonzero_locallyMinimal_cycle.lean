-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_exists_nonzero_locallyMinimal_cycle
-- name    : QEC.Coding.LocallyMinimalDistance.exists_nonzero_locallyMinimal_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:04.291032+00:00
-- url     : https://prove2.me/theorems/92111159-0b7c-4b83-9ab2-ad127e86e5fa
-- title:
--   Locally Minimal Distance: exists nonzero locally Minimal cycle
-- statement:
--   A non-boundary cycle has a nonzero, locally minimal coset representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L54-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L54-L72

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.exists_nonzero_locallyMinimal_cycle
    (weight : C → Nat) (Z B : AddSubgroup C) (moves : Finset C)
    (hBZ : B ≤ Z) (hmoves : ∀ m ∈ moves, m ∈ B)
    (c : C) (hcZ : c ∈ Z) (hcB : c ∉ B) :
    ∃ c' : C, c' ∈ Z ∧ c' ≠ 0 ∧ IsLocallyMinimal weight moves c' ∧
      weight c' ≤ weight c := by sorry
