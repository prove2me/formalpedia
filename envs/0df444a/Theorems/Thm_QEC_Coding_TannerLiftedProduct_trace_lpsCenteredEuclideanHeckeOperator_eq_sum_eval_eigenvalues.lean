-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- name    : QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:19.470193+00:00
-- url     : https://prove2.me/theorems/8f3461e9-ef28-4dde-9fc1-ef6c704a5a82
-- title:
--   Tanner Lifted Product: trace lps Centered Euclidean Hecke Operator eq sum eval eigenvalues
-- statement:
--   The Euclidean centered LPS Hecke trace is the sum of the Hecke
--   polynomial over the real centered-adjacency eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L196-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L196-L206

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

theorem QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℂ (p : ℂ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i : ℂ) := by sorry
