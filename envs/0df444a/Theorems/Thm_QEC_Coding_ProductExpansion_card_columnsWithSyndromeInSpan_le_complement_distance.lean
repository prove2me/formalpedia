-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_columnsWithSyndromeInSpan_le_complement_distance
-- name    : QEC.Coding.ProductExpansion.card_columnsWithSyndromeInSpan_le_complement_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:33.125736+00:00
-- url     : https://prove2.me/theorems/4b7d2c83-a126-446a-a0e6-378c9f4b3cc2
-- title:
--   Product Expansion: card columns With Syndrome In Span le complement distance
-- statement:
--   At most `w-d` columns can have syndromes in the span of a generator
--   family whose restricted total weight is below `d/6`. Thus at least `d`
--   columns require a generator outside that light family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1481-L1521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1481-L1521

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

theorem QEC.Coding.ProductExpansion.card_columnsWithSyndromeInSpan_le_complement_distance
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    (columnsWithSyndromeInSpan h' x C).card ≤ Fintype.card W - d := by sorry
