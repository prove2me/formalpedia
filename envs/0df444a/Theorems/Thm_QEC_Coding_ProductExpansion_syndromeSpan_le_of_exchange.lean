-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_syndromeSpan_le_of_exchange
-- name    : QEC.Coding.ProductExpansion.syndromeSpan_le_of_exchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:07.256261+00:00
-- url     : https://prove2.me/theorems/4bb74d0e-8827-4403-885c-7e4fe9d5b857
-- title:
--   Product Expansion: syndrome Span le of exchange
-- statement:
--   Replacing one word representative by a word whose syndrome has a
--   nonzero coordinate at that representative preserves the span of all original
--   syndromes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1049-L1084
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1049-L1084

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

theorem QEC.Coding.ProductExpansion.syndromeSpan_le_of_exchange
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ a : C, (b a).1 = h'.mulVec a.1)
    (c : C) (y : Word F W)
    (hy : h'.mulVec y ∈ syndromeSpan h' C)
    (hCoordinate : (b.repr ⟨h'.mulVec y, hy⟩) c ≠ 0) :
    syndromeSpan h' C ≤ syndromeSpan h' (insert y (C.erase c.1)) := by sorry
