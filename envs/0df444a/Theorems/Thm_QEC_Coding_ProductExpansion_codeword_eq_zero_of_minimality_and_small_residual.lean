-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_minimality_and_small_residual
-- name    : QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_small_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:24:56.487404+00:00
-- url     : https://prove2.me/theorems/c51a4045-3ad1-4aa1-a7f7-78e21572fd72
-- title:
--   Product Expansion: codeword eq zero of minimality and small residual
-- statement:
--   A near-minimal word cannot be shortened to a light residual by subtracting
--   a nonzero codeword when twice that residual weight plus the allowed decrease
--   is below the code distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L324-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L324-L345

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_small_residual
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (x c : Word F W)
    (hc : c ∈ (parityCheckCode h).carrier)
    (hGap : 2 * (HammingWeight (x - c) : ℝ) + delta < d)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by sorry
