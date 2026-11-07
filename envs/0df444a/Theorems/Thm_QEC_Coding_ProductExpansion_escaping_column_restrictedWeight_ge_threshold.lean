-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_escaping_column_restrictedWeight_ge_threshold
-- name    : QEC.Coding.ProductExpansion.escaping_column_restrictedWeight_ge_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:30.659748+00:00
-- url     : https://prove2.me/theorems/ad273f5d-ea76-47f0-af2b-e16dc540d6d4
-- title:
--   Product Expansion: escaping column restricted Weight ge threshold
-- statement:
--   Every column whose syndrome escapes the light-generator span has
--   restricted weight at least the light/heavy threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1791-L1816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1791-L1816

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
omit [Fintype F] [Fintype R]

theorem QEC.Coding.ProductExpansion.escaping_column_restrictedWeight_ge_threshold
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (j : W) (hj : j ∈ columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) :
    d ≤ 6 * C.card * restrictedHammingWeight A (column x j) := by sorry
