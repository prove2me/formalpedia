-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_vanish_outside_generatorSupport_of_small_weight
-- name    : QEC.Coding.ProductExpansion.column_vanish_outside_generatorSupport_of_small_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:38.643515+00:00
-- url     : https://prove2.me/theorems/eff54b60-bc97-4aa3-aa4d-4f27ace96784
-- title:
--   Product Expansion: column vanish outside generator Support of small weight
-- statement:
--   If the selected generators have total restricted weight below `d/6`,
--   every matrix column whose syndrome lies in their span is supported inside
--   their common support union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1288-L1310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1288-L1310

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

theorem QEC.Coding.ProductExpansion.column_vanish_outside_generatorSupport_of_small_weight
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6)
    (j : W) (hSyndrome : h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    ∀ i ∉ generatorSupport C, x i j = 0 := by sorry
