-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_cusp_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:10.262839+00:00
-- url     : https://prove2.me/theorems/5bccbc3c-6f3c-4dd8-b7c9-8b41296c04ef
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function cusp analytic
-- statement:
--   Nonnegative actual cusp orders make the normalized cusp representatives analytic at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L78-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L78-L98

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun q => lpsOriginalNormalizedFilledFunction N hN F
      ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by sorry
