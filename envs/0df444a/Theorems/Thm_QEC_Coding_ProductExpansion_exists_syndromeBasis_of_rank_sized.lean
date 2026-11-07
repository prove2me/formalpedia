-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_syndromeBasis_of_rank_sized
-- name    : QEC.Coding.ProductExpansion.exists_syndromeBasis_of_rank_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:28.235764+00:00
-- url     : https://prove2.me/theorems/5aec9ccb-43a1-465a-a8a0-b80d2fda82ad
-- title:
--   Product Expansion: exists syndrome Basis of rank sized
-- statement:
--   Package the rank-sized generating syndromes as a basis indexed by the
--   actual representative words. This exposes basis coordinates for the exchange
--   step of the rank argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L946-L980
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L946-L980

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

theorem QEC.Coding.ProductExpansion.exists_syndromeBasis_of_rank_sized
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    ∃ b : Module.Basis C F (syndromeSpan h' C),
      ∀ c : C, (b c).1 = h'.mulVec c.1 := by sorry
