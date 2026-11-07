-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_generator_coordinate_outside_span
-- name    : QEC.Coding.ProductExpansion.exists_generator_coordinate_outside_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:57.584251+00:00
-- url     : https://prove2.me/theorems/e09be0fa-6fd5-4b46-a442-8a9940d5316e
-- title:
--   Product Expansion: exists generator coordinate outside span
-- statement:
--   A syndrome outside the span of selected generators has a nonzero basis
--   coordinate on some generator outside that selection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L985-L1009
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L985-L1009

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.exists_generator_coordinate_outside_span
    (h' : Matrix R' W F) (C T : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (hb : ∀ c : C, (b c).1 = h'.mulVec c.1)
    (z : syndromeSpan h' C)
    (hz : (z.1 : R' → F) ∉ syndromeSpan h' T) :
    ∃ c : C, c.1 ∉ T ∧ (b.repr z) c ≠ 0 := by sorry
