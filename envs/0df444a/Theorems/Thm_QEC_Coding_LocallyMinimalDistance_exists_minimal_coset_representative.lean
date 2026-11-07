-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_exists_minimal_coset_representative
-- name    : QEC.Coding.LocallyMinimalDistance.exists_minimal_coset_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:42.774537+00:00
-- url     : https://prove2.me/theorems/e41aaacf-7378-46c6-8f7d-390c9f3c0af6
-- title:
--   Locally Minimal Distance: exists minimal coset representative
-- statement:
--   A finite-weight coset has a representative attaining its quotient weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L32-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L32-L38

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.exists_minimal_coset_representative
    (weight : C → Nat) (B : AddSubgroup C) (c : C) :
    ∃ b ∈ B, weight (c + b) = cosetWeight weight B c := by sorry
