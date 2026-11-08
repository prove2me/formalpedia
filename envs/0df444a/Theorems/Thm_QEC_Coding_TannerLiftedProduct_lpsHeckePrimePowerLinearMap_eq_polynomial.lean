-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePrimePowerLinearMap_eq_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePrimePowerLinearMap_eq_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:52.71575+00:00
-- url     : https://prove2.me/theorems/ce1bf833-21a6-4c42-9a99-ccc242182bfc
-- title:
--   Tanner Lifted Product: lps Hecke Prime Power Linear Map eq polynomial
-- statement:
--   The recursive endomorphism is evaluation of the existing Hecke polynomial at the actual operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L278-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L278-L293

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePrimePowerLinearMap_eq_polynomial (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) :
    lpsHeckePrimePowerLinearMap N p hNp r=
      (lpsHeckePolynomial ℂ (p:ℂ) r).eval₂
        (algebraMap ℂ (Module.End ℂ (CuspForm
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
        (lpsCuspHeckeLinearMap N p hNp) := by sorry
