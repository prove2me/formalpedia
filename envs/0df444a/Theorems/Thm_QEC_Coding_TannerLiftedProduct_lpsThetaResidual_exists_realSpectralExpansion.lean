-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaResidual_exists_realSpectralExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realSpectralExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:35:54.754803+00:00
-- url     : https://prove2.me/theorems/680703e6-a8ed-40bd-b4f2-f17ec47fe3fa
-- title:
--   Tanner Lifted Product: lps Theta Residual exists real Spectral Expansion
-- statement:
--   The ORIGINAL centered theta residual has a derived finite real Hecke spectral expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRealSpectrum.lean#L18-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRealSpectrum.lean#L18-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRealSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaResidual_exists_realSpectralExpansion (p : ℕ) (a : LPSResiduePrime p) :
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∃c : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℂ,
    ∀n : ℕ,lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (∑i,c i*(lpsHeckePolynomial ℂ (p:ℂ) (2*n)).eval (eigenvalue i:ℂ)).re+2*(-(p:ℝ))^n := by sorry
