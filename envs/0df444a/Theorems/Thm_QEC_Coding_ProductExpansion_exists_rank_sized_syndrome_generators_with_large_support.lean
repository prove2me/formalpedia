-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_rank_sized_syndrome_generators_with_large_support
-- name    : QEC.Coding.ProductExpansion.exists_rank_sized_syndrome_generators_with_large_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:59:30.385817+00:00
-- url     : https://prove2.me/theorems/4b20d260-c4ec-46e5-9192-f713dcaf1398
-- title:
--   Product Expansion: exists rank sized syndrome generators with large support
-- statement:
--   For a nonzero `d/3`-minimal product codeword, a rank-sized finite
--   syndrome-generating family can be chosen and its support union has size at
--   least `d/3`. The quantitative rank lemma next minimizes this family's
--   restricted weight and counts its heavy representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1975-L1994
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1975-L1994

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

theorem QEC.Coding.ProductExpansion.exists_rank_sized_syndrome_generators_with_large_support
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 3 ≤ (generatorSupport C).card ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) := by sorry
