-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_nonzeroRowsOnColumns_ge_one_third_distance
-- name    : QEC.Coding.ProductExpansion.card_nonzeroRowsOnColumns_ge_one_third_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:44.947378+00:00
-- url     : https://prove2.me/theorems/653c0c11-b34d-49e8-b1b1-c958975128e1
-- title:
--   Product Expansion: card nonzero Rows On Columns ge one third distance
-- statement:
--   Every sufficiently large selection of columns of a nonzero minimal
--   product codeword meets at least `d/3` rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1401-L1438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1401-L1438

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

theorem QEC.Coding.ProductExpansion.card_nonzeroRowsOnColumns_ge_one_third_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (B : Finset W) (hSizeB : Fintype.card W - d < B.card) :
    (d : ℝ) / 3 ≤ (nonzeroRowsOnColumns x B).card := by sorry
