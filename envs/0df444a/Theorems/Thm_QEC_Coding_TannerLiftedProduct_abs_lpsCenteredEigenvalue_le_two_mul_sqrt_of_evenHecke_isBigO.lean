-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:32.825794+00:00
-- url     : https://prove2.me/theorems/178eeac3-bc0a-4501-96f9-09a3e2d4721b
-- title:
--   Tanner Lifted Product: abs lps Centered Eigenvalue le two mul sqrt of even Hecke is Big O
-- statement:
--   Specialized sharp-growth criterion for one centered LPS adjacency
--   eigenvalue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L140-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L140-L152

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric

set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
    (a : LPSResiduePrime p)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (h : ∀ t : ℝ, Real.sqrt (p : ℝ) < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
        =O[atTop] fun n : ℕ => t ^ (2 * n)) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) := by sorry
