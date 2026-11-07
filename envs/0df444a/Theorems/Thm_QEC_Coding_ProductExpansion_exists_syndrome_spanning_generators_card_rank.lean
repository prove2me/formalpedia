-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_syndrome_spanning_generators_card_rank
-- name    : QEC.Coding.ProductExpansion.exists_syndrome_spanning_generators_card_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:27:20.884011+00:00
-- url     : https://prove2.me/theorems/548636b1-e8ae-411f-9004-8813ac251386
-- title:
--   Product Expansion: exists syndrome spanning generators card rank
-- statement:
--   A syndrome matrix has a finite family of word representatives, with
--   exactly its matrix rank many members, whose syndromes span all its columns.
--   This is the algebraic generator choice before the source minimizes their
--   restricted weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1656-L1709
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1656-L1709

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

theorem QEC.Coding.ProductExpansion.exists_syndrome_spanning_generators_card_rank
    (h' : Matrix R' W F) (x : Matrix W W F) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) := by sorry
