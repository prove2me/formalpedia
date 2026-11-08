-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_exists_realEigenBasis
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realEigenBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:03:20.538278+00:00
-- url     : https://prove2.me/theorems/792f9c01-7d9b-46f4-adb5-162ce46e4383
-- title:
--   Tanner Lifted Product: lps Cusp Hecke exists real Eigen Basis
-- statement:
--   Positive genuine Petersson pairing, true adjunction and proved finite dimension give real eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L34-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean#L34-L57

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

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_exists_realEigenBasis (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    ∀i,lpsCuspHeckeLinearMap N p hNp (b i)=(eigenvalue i:ℂ) • b i := by sorry
