-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_exists_realCoefficientExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realCoefficientExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:51.360195+00:00
-- url     : https://prove2.me/theorems/a5df7848-952b-4ac5-8312-5419a90e0953
-- title:
--   Tanner Lifted Product: lps Cusp Hecke exists real Coefficient Expansion
-- statement:
--   Real spectral expansion of the ORIGINAL cusp space is derived, not an eigenbasis supplied by a caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L99-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L99-L113

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

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realCoefficientExpansion (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    (∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i) ∧
    ∀r (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f)=
      ∑i,b.repr f i*(lpsHeckePolynomial ℂ (p:ℂ) r).eval (eigenvalue i:ℂ)*
        PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (b i)) := by sorry
