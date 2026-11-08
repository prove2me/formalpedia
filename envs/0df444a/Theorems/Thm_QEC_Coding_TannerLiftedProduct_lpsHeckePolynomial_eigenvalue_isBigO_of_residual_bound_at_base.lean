-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:56:33.887193+00:00
-- url     : https://prove2.me/theorems/deee065b-236b-45c5-9dd5-719e3e0aee8b
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eigenvalue is Big O of residual bound at base
-- statement:
--   The optimal centered theta coefficient estimate gives every individual
--   centered eigenvalue the Hecke growth required by the sharp analytic
--   endgame.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L415-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L415-L477

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

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
    (a : LPSResiduePrime p) (base : ℝ) (hBase : (p : ℝ) ≤ base)
    (C : ℝ) (hC : 0 ≤ C)
    (hResidual : ∀ n : ℕ,
      |lpsCenteredThetaResidual a (2 * n)| ≤
        C * (((2 * n + 1 : ℕ) : ℝ) * base ^ n))
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (t : ℝ) (ht : Real.sqrt base < t) :
    (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ => t ^ (2 * n) := by sorry
