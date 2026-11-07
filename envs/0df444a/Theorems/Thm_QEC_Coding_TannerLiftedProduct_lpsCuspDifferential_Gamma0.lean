-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_Gamma0
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_Gamma0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:26.793067+00:00
-- url     : https://prove2.me/theorems/956404fc-df4d-4146-9bc6-103e2b03da57
-- title:
--   Tanner Lifted Product: lps Cusp Differential Gamma0
-- statement:
--   The actual original differential is invariant under true Gamma0 tangent pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L49-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L49-L61

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_Gamma0 (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N f (g • τ)
      (deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) =
    lpsCuspDifferential N f τ v := by sorry
