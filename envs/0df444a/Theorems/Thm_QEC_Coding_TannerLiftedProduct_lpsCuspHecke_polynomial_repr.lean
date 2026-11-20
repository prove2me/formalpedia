-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_polynomial_repr
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_polynomial_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:49:12.590456+00:00
-- url     : https://prove2.me/theorems/455ea1e0-84ba-4dfb-9964-9124c0a32fff
-- title:
--   Tanner Lifted Product: lps Cusp Hecke polynomial repr
-- statement:
--   A genuine original Hecke eigenbasis diagonalizes every actual polynomial action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L43-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L43-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_polynomial_repr (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) {I : Type*} [Fintype I]
    (b : Module.Basis I ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))
    (eigenvalue : I→ℝ)
    (hb : ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i)
    (P : ℂ[X]) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : I) :
    b.repr ((aeval (lpsCuspHeckeLinearMap N p hNp) P) f) i =
      b.repr f i * P.eval (eigenvalue i:ℂ) := by sorry
