-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_lpsResiduePrime_gt
-- name    : QEC.Coding.TannerLiftedProduct.exists_lpsResiduePrime_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:50.110315+00:00
-- url     : https://prove2.me/theorems/ef4f4587-d621-49ba-b1ee-6d6321af29b7
-- title:
--   Tanner Lifted Product: exists lps Residue Prime gt
-- statement:
--   There are source-compatible residue primes above every bound.  The
--   progression `q = 1 mod 4p` simultaneously enforces `q = 1 mod 4` and
--   `q = 1 mod p`; quadratic reciprocity then gives `(p/q) = 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L203-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L203-L231

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

theorem QEC.Coding.TannerLiftedProduct.exists_lpsResiduePrime_gt
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    ∃ a : LPSResiduePrime p, B < a.q := by sorry
