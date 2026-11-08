-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferential_Hecke_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_Hecke_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:09:05.852193+00:00
-- url     : https://prove2.me/theorems/be2155e7-6201-4fd4-8ef0-905dbdc9fdc6
-- title:
--   Tanner Lifted Product: lps Original Filled Differential Hecke pullback
-- statement:
--   The original p+1 Hecke sum is preserved through the genuine orbit-projection tangent pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L314-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L314-L342

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_Hecke_pullback (N p : ℕ) [NeZero N]
    (hN : 4∣N) [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
    lpsOriginalFilledDifferentialLinearMap N hN (lpsCuspHeckeLinearMap N p hNp f) (proj τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ v) =
      ∑i : Option (Fin p),lpsOriginalFilledDifferentialLinearMap N hN f
        (proj (lpsHeckeUpperGL ℝ p i • τ))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj (lpsHeckeUpperGL ℝ p i • τ)
          (deriv (fun z : ℂ => (lpsHeckeUpperGL ℝ p i • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v)) := by sorry
