-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generatorRestrictedWeight_ge_one_sixth_of_large_support
-- name    : QEC.Coding.ProductExpansion.generatorRestrictedWeight_ge_one_sixth_of_large_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:30.124916+00:00
-- url     : https://prove2.me/theorems/cf1f0bb2-8e7f-4501-9da9-1a55c4c0dcdb
-- title:
--   Product Expansion: generator Restricted Weight ge one sixth of large support
-- statement:
--   The paper's support-union counting step: if the common support has size
--   at least `d/3` and at most `m ≤ d/6` coordinates lie outside `A`, the total
--   restricted generator weight is at least `d/6`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1227-L1252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1227-L1252

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

theorem QEC.Coding.ProductExpansion.generatorRestrictedWeight_ge_one_sixth_of_large_support
    (d m : Nat) (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hSupport : (d : ℝ) / 3 ≤ (generatorSupport C).card) :
    (d : ℝ) / 6 ≤ generatorRestrictedWeight A C := by sorry
