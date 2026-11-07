-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:45:56.246371+00:00
-- url     : https://prove2.me/theorems/9542f204-6f82-46f7-b07f-5bc005c7baae
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient analytic
-- statement:
--   The original removable cusp differential coefficient is analytic on the entire unit disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L115-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L115-L141

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analytic (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) (hq : ‖q‖<1) :
    AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) q := by sorry
