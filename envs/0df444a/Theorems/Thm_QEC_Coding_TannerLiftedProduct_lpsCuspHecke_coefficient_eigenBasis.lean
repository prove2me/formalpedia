-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_coefficient_eigenBasis
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_coefficient_eigenBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:48.617176+00:00
-- url     : https://prove2.me/theorems/481b8525-4ffe-401d-b083-0d3022bf0d91
-- title:
--   Tanner Lifted Product: lps Cusp Hecke coefficient eigen Basis
-- statement:
--   The original prime-power Fourier coefficient is the real-eigenbasis polynomial sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L82-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L82-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_coefficient_eigenBasis (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) {I : Type*} [Fintype I]
    (b : Module.Basis I ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))
    (eigenvalue : I→ℝ) (hb : ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i)
    (r : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) =
      ∑i,b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)*
        PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)) := by sorry
