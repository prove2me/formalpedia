-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasOptimalCenteredThetaCoefficientBound_iff_ramanujan
-- name    : QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_iff_ramanujan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:05:14.134872+00:00
-- url     : https://prove2.me/theorems/f52283d5-7c58-473e-8802-1252c78bcf8a
-- title:
--   Tanner Lifted Product: has Optimal Centered Theta Coefficient Bound iff ramanujan
-- statement:
--   The centered theta coefficient estimate is equivalent to the full
--   Ramanujan eigenvalue bound for this finite LPS graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L581-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L581-L591

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

theorem QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_iff_ramanujan
    (a : LPSResiduePrime p) :
    HasOptimalCenteredThetaCoefficientBound a ↔
      ∀ i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
          2 * Real.sqrt (p : ℝ) := by sorry
