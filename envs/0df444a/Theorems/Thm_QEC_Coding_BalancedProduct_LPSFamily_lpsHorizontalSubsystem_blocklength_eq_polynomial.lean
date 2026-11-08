-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_lpsHorizontalSubsystem_blocklength_eq_polynomial
-- name    : QEC.Coding.BalancedProduct.LPSFamily.lpsHorizontalSubsystem_blocklength_eq_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:05.022578+00:00
-- url     : https://prove2.me/theorems/c5c9e39e-91df-4d16-95f4-04c67d379d9c
-- title:
--   LPSFamily: lps Horizontal Subsystem blocklength eq polynomial
-- statement:
--   The corrected BE20 blocklength is the exact cubic polynomial
--   `401 q (q^2-1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L175-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean#L175-L186

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.LPSFamily.lpsHorizontalSubsystem_blocklength_eq_polynomial
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
          (Cyclic.CyclicGroup q)) =
      401 * q * (q ^ 2 - 1) := by sorry
