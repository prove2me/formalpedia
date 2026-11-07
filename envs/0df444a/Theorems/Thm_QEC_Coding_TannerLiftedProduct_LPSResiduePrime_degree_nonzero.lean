-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_degree_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.degree_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:49.908984+00:00
-- url     : https://prove2.me/theorems/60dcc5ba-fa2c-4e62-a50d-76b79966a38c
-- title:
--   LPSResidue Prime: degree nonzero
-- statement:
--   The LPSResidue Prime construction uses the degree nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L142-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L142-L149

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

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.degree_nonzero (a : LPSResiduePrime p) :
    (p : ZMod a.q) ≠ 0 := by sorry
