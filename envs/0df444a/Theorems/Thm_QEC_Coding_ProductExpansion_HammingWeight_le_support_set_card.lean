-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_support_set_card
-- name    : QEC.Coding.ProductExpansion.HammingWeight_le_support_set_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:09.856192+00:00
-- url     : https://prove2.me/theorems/8d8e463a-0eaa-4da6-8989-e08997a44633
-- title:
--   Product Expansion: Hamming Weight le support set card
-- statement:
--   A word supported inside a finite set has weight at most its cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L292-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L292-L301

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

theorem QEC.Coding.ProductExpansion.HammingWeight_le_support_set_card
    (S : Finset W) (x : Word F W) (hSupport : ∀ i ∉ S, x i = 0) :
    HammingWeight x ≤ S.card := by sorry
