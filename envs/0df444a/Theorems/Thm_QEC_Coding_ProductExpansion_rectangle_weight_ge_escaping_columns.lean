-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_rectangle_weight_ge_escaping_columns
-- name    : QEC.Coding.ProductExpansion.rectangle_weight_ge_escaping_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:01.727916+00:00
-- url     : https://prove2.me/theorems/2f4e3829-cdfb-40d2-afb9-780eca32621b
-- title:
--   Product Expansion: rectangle weight ge escaping columns
-- statement:
--   Summing the weight threshold over the escaping columns contained in a
--   rectangle gives the counting inequality for the PK22 rank bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1821-L1856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1821-L1856

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

theorem QEC.Coding.ProductExpansion.rectangle_weight_ge_escaping_columns
    [DecidableEq W]
    (h' : Matrix R' W F) (x : Matrix W W F) (A B : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) :
    d * ((columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) ∩ B).card ≤
      6 * C.card * restrictedWeight x A B := by sorry
