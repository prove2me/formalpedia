-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_one_lpsHeckePrimePowerLinearMap
-- name    : QEC.Coding.TannerLiftedProduct.coeff_one_lpsHeckePrimePowerLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:20.565641+00:00
-- url     : https://prove2.me/theorems/60bbfbc5-5d25-4677-b7e7-aaaaf0ec5466
-- title:
--   Tanner Lifted Product: coeff one lps Hecke Prime Power Linear Map
-- statement:
--   The first coefficient of each constructed endomorphism recovers a(p^r) for every cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L249-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L249-L275

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_one_lpsHeckePrimePowerLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsHeckePrimePowerLinearMap N p hNp r f))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by sorry
