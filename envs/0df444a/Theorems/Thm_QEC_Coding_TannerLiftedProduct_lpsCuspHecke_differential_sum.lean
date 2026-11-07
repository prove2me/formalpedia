-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_differential_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_differential_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:43.906085+00:00
-- url     : https://prove2.me/theorems/e7f25091-4d6b-41db-9314-48c12ccdb110
-- title:
--   Tanner Lifted Product: lps Cusp Hecke differential sum
-- statement:
--   The original Hecke differential is the actual sum of p+1 tangent pullbacks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L64-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean#L64-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_differential_sum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N (lpsCuspHeckeLinearMap N p hNp f) τ v =
      ∑i : Option (Fin p),lpsCuspDifferential N f (lpsHeckeUpperGL ℝ p i • τ)
        (deriv (fun z : ℂ => (lpsHeckeUpperGL ℝ p i • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) := by sorry
