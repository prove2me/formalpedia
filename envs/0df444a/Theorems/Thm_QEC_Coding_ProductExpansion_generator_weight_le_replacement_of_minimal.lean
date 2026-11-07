-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generator_weight_le_replacement_of_minimal
-- name    : QEC.Coding.ProductExpansion.generator_weight_le_replacement_of_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:32.304197+00:00
-- url     : https://prove2.me/theorems/e4d42a13-5e13-4c53-8693-a9d3f4ee7609
-- title:
--   Product Expansion: generator weight le replacement of minimal
-- statement:
--   Minimum total restricted weight turns a valid basis exchange into a
--   pointwise lower bound on the replacement column's restricted weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1745-L1786
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1745-L1786

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
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.generator_weight_le_replacement_of_minimal
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (j : W)
    (hCoordinate : (b.repr ⟨h'.mulVec (column x j), hSpanning j⟩) c ≠ 0) :
    restrictedHammingWeight A c.1 ≤ restrictedHammingWeight A (column x j) := by sorry
