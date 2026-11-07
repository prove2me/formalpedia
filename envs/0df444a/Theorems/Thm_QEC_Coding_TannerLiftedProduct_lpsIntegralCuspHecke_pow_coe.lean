-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspHecke_pow_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_pow_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:08:41.900611+00:00
-- url     : https://prove2.me/theorems/aa05144e-49f3-4963-b8ef-f2c71eaf3677
-- title:
--   Tanner Lifted Product: lps Integral Cusp Hecke pow coe
-- statement:
--   Inclusion intertwines every power of the actual restricted and original Hecke operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L122-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L122-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_pow_coe (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) (f : lpsIntegralCuspLattice N) :
    (((lpsIntegralCuspHecke N p hNp)^r) f :
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) =
      ((lpsCuspHeckeLinearMap N p hNp)^r) f.val := by sorry
