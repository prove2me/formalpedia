-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_eq_small_support_syndrome_lift
-- name    : QEC.Coding.ProductExpansion.column_eq_small_support_syndrome_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:25.813208+00:00
-- url     : https://prove2.me/theorems/cb7c161d-accb-49c7-9846-14b44430ab0f
-- title:
--   Product Expansion: column eq small support syndrome lift
-- statement:
--   A small-support lift of a column's syndrome must equal that column in a
--   `d/3`-minimal matrix. This is the source's first rank-lemma contradiction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L448-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L448-L477

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

theorem QEC.Coding.ProductExpansion.column_eq_small_support_syndrome_lift
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (S : Finset W) (hSmall : (S.card : ℝ) < (d : ℝ) / 3)
    (j : W) (y : Word F W)
    (hSupport : ∀ i ∉ S, y i = 0)
    (hSyndrome : h'.mulVec y = h'.mulVec (column x j)) :
    column x j = y := by sorry
