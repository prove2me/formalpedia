-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaResidual_exists_realIntegralSpectralExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realIntegralSpectralExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:49:44.616395+00:00
-- url     : https://prove2.me/theorems/ed93c621-8210-40ed-9bd5-8493b9e57c5f
-- title:
--   Tanner Lifted Product: lps Theta Residual exists real Integral Spectral Expansion
-- statement:
--   The ORIGINAL centered theta expansion has algebraic-integer eigenvalues on every active term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L91-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L91-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realIntegralSpectralExpansion (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    (∀i,c i≠0 → IsIntegral ℤ (eigenvalue i:ℂ)) ∧
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by sorry
