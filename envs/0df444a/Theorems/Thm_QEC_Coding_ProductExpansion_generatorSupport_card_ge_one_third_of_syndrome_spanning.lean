-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generatorSupport_card_ge_one_third_of_syndrome_spanning
-- name    : QEC.Coding.ProductExpansion.generatorSupport_card_ge_one_third_of_syndrome_spanning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:27:15.420557+00:00
-- url     : https://prove2.me/theorems/1ef5b7f2-1444-45c7-8ec6-d629e3890ab8
-- title:
--   Product Expansion: generator Support card ge one third of syndrome spanning
-- statement:
--   A finite family whose syndromes span all columns of `h' * x` must have
--   support union of size at least `d/3`. This discharges the lift hypothesis of
--   the preceding lemma using the actual linear span of generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1628-L1649
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1628-L1649

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

theorem QEC.Coding.ProductExpansion.generatorSupport_card_ge_one_third_of_syndrome_spanning
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (C : Finset (Word F W))
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    (d : ℝ) / 3 ≤ (generatorSupport C).card := by sorry
