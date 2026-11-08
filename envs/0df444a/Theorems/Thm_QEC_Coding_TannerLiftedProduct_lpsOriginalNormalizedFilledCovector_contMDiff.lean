-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_contMDiff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_contMDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:48:45.555487+00:00
-- url     : https://prove2.me/theorems/59c17cbf-8dcc-45f4-ae3c-b3ffd46f31fc
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Covector cont MDiff
-- statement:
--   Actual no-pole orders at every own-chart center make the repaired Hom-bundle section analytic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L38-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean#L38-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_contMDiff
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (horder : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x x)) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : LPSOriginalFilledCurve N => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun y : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) y →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ y)
        x (lpsOriginalNormalizedFilledCovector N hN sigma x)) := by sorry
