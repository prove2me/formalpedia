-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_min_weight_generators_with_large_support
-- name    : QEC.Coding.ProductExpansion.exists_min_weight_generators_with_large_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:42.063571+00:00
-- url     : https://prove2.me/theorems/42ad1eb8-1039-4871-9d8d-7f37a62a83ae
-- title:
--   Product Expansion: exists min weight generators with large support
-- statement:
--   The source's minimum-weight syndrome representatives exist, have exactly
--   the syndrome rank many members, and their support union already satisfies the
--   first `d/3` lower bound used in the rank argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L2000-L2024
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L2000-L2024

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

theorem QEC.Coding.ProductExpansion.exists_min_weight_generators_with_large_support
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 3 ≤ (generatorSupport C).card ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by sorry
