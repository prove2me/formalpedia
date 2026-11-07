-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_differential_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_differential_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:57.774417+00:00
-- url     : https://prove2.me/theorems/c9a48bb2-776d-4393-88be-e919214f8130
-- title:
--   Tanner Lifted Product: lps Original Cusp Coordinate differential pullback
-- statement:
--   The actual cusp coordinate pulls its minimal-width differential back to the original form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L145-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L145-L179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_differential_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    lpsOriginalCuspQCoefficient N f ρ (Φ τ) * deriv Φ τ = f τ := by sorry
