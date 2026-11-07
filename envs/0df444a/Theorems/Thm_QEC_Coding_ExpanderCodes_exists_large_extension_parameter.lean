-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_large_extension_parameter
-- name    : QEC.Coding.ExpanderCodes.exists_large_extension_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:31:01.206925+00:00
-- url     : https://prove2.me/theorems/b4680eb3-11db-41dc-8387-c9165e31e964
-- title:
--   Expander Codes: exists large extension parameter
-- statement:
--   Fixed-characteristic extension fields are arbitrarily large, with a
--   genuine irreducible specialization parameter of degree greater than two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSpecialization.lean#L53-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSpecialization.lean#L53-L62

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.exists_large_extension_parameter (p N : ℕ) [hPrime : Fact p.Prime] :
    ∃ n : ℕ, 2 < n ∧ N ≤ Nat.card (GaloisField p n) ∧
      ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
        Irreducible (minpoly (ZMod p) y) ∧
        (minpoly (ZMod p) y).natDegree = n ∧
        adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by sorry
