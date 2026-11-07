-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:55.679533+00:00
-- url     : https://prove2.me/theorems/28c76aa4-6254-4148-906c-8d80d0bf6e22
-- title:
--   Tanner Lifted Product: lps Cusp Differential apply
-- statement:
--   The actual differential evaluated on a complex tangent vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L23-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L23-L25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_apply (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) : lpsCuspDifferential N f τ v = f τ*v := by sorry
