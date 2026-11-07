-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_syndromeGenerators_linearIndependent_of_rank_sized
-- name    : QEC.Coding.ProductExpansion.syndromeGenerators_linearIndependent_of_rank_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:07.115873+00:00
-- url     : https://prove2.me/theorems/48aa3c8b-162d-4a11-9c05-8c36c1294514
-- title:
--   Product Expansion: syndrome Generators linear Independent of rank sized
-- statement:
--   The syndromes of a rank-sized spanning family are linearly independent,
--   so they form a genuine basis of the syndrome column space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L919-L940
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L919-L940

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

theorem QEC.Coding.ProductExpansion.syndromeGenerators_linearIndependent_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    LinearIndependent F (fun c : C => h'.mulVec c.1) := by sorry
