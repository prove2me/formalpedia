-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_two_mul_card_psl
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.two_mul_card_psl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:42.527843+00:00
-- url     : https://prove2.me/theorems/f89e5eca-b88d-4a51-93d8-ec8440bd308e
-- title:
--   LPSResidue Prime: two mul card psl
-- statement:
--   The bipartite double cover has exactly `q(q²-1)` vertices, matching the
--   `n` used in PK22 Example 2.4 and Lemma 3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L184-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L184-L198

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.two_mul_card_psl (a : LPSResiduePrime p) :
    2 * Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) := by sorry
