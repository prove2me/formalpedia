-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_complement_card
-- name    : QEC.Coding.ProductExpansion.HammingWeight_le_complement_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:09.859512+00:00
-- url     : https://prove2.me/theorems/1d29133d-92ac-4949-8097-c2b2304f12ee
-- title:
--   Product Expansion: Hamming Weight le complement card
-- statement:
--   A word vanishing on `A` is supported on at most the complement of `A`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L275-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L275-L288

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

theorem QEC.Coding.ProductExpansion.HammingWeight_le_complement_card
    (A : Finset W) (x : Word F W) (hVanish : ∀ j ∈ A, x j = 0) :
    HammingWeight x ≤ Fintype.card W - A.card := by sorry
