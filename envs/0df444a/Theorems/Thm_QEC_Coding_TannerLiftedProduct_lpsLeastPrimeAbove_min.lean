-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsLeastPrimeAbove_min
-- name    : QEC.Coding.TannerLiftedProduct.lpsLeastPrimeAbove_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:54.087194+00:00
-- url     : https://prove2.me/theorems/fca5edd9-04f5-46bc-a24e-e9db3a38f172
-- title:
--   Tanner Lifted Product: lps Least Prime Above min
-- statement:
--   The Tanner Lifted Product construction uses the lps Least Prime Above min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L259-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L259-L261

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

theorem QEC.Coding.TannerLiftedProduct.lpsLeastPrimeAbove_min {p : ℕ} (hp : p.Prime) (B q : ℕ)
    (hq : lpsPrimeCandidate p B q) : lpsLeastPrimeAbove hp B ≤ q := by sorry
