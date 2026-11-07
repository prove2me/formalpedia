-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_syndromeSpan_eq_matrix_range_of_rank_sized
-- name    : QEC.Coding.ProductExpansion.syndromeSpan_eq_matrix_range_of_rank_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:04.735573+00:00
-- url     : https://prove2.me/theorems/38575f82-3519-4a55-a8fd-10a64f82226a
-- title:
--   Product Expansion: syndrome Span eq matrix range of rank sized
-- statement:
--   A rank-sized family whose syndromes span every column spans exactly the
--   column space of `h' * x`; it cannot hide extraneous syndrome directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L882-L914
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L882-L914

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

theorem QEC.Coding.ProductExpansion.syndromeSpan_eq_matrix_range_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    syndromeSpan h' C = LinearMap.range (h' * x).mulVecLin := by sorry
