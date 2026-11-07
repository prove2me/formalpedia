-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_sub_le
-- name    : QEC.Coding.ProductExpansion.HammingWeight_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:20.560812+00:00
-- url     : https://prove2.me/theorems/31fc3cc7-c23a-4e74-a2dd-5731f011123b
-- title:
--   Product Expansion: Hamming Weight sub le
-- statement:
--   A Hamming-weight triangle inequality for subtraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L312-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L312-L318

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

theorem QEC.Coding.ProductExpansion.HammingWeight_sub_le (x y : Word F W) :
    HammingWeight (x - y) ≤ HammingWeight x + HammingWeight y := by sorry
