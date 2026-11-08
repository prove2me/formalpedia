-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasOptimalCenteredThetaCoefficientBound_of_ramanujan
-- name    : QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_of_ramanujan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:00:39.713004+00:00
-- url     : https://prove2.me/theorems/b916127f-63cc-475c-9346-9a79e1014705
-- title:
--   Tanner Lifted Product: has Optimal Centered Theta Coefficient Bound of ramanujan
-- statement:
--   Conversely, the Ramanujan interval bounds the centered theta residual.
--   The coefficient is just the finite number of centered adjacency eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L541-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L541-L577

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

theorem QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_of_ramanujan
    (a : LPSResiduePrime p)
    (hRamanujan : ∀ i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))),
      |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
        2 * Real.sqrt (p : ℝ)) :
    HasOptimalCenteredThetaCoefficientBound a := by sorry
