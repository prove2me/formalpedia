-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_vanish_on_large_subset
-- name    : QEC.Coding.ProductExpansion.codeword_eq_zero_of_vanish_on_large_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:08.063193+00:00
-- url     : https://prove2.me/theorems/6244aa2e-a2b2-447b-942a-bdcb9ae3326c
-- title:
--   Product Expansion: codeword eq zero of vanish on large subset
-- statement:
--   A set larger than `w-d` separates all codewords when the code distance is at least `d`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L70-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L70-L92

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]

theorem QEC.Coding.ProductExpansion.codeword_eq_zero_of_vanish_on_large_subset
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hVanish : ∀ i ∈ A, c i = 0) : c = 0 := by sorry
