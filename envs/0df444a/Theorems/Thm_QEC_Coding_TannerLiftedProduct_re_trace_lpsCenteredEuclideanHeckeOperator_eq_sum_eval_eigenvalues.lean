-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- name    : QEC.Coding.TannerLiftedProduct.re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:07.419798+00:00
-- url     : https://prove2.me/theorems/a6df6c97-fd90-4be6-828b-24cee71b6aa2
-- title:
--   Tanner Lifted Product: re trace lps Centered Euclidean Hecke Operator eq sum eval eigenvalues
-- statement:
--   Real form of the preceding spectral trace identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L209-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L209-L222

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

theorem QEC.Coding.TannerLiftedProduct.re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    Complex.re (LinearMap.trace ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n)) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) := by sorry
