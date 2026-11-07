-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsCuspHecke_prime_power
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsCuspHecke_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:09.248389+00:00
-- url     : https://prove2.me/theorems/3c54f480-b423-4078-ade1-ab7c4b98c5c8
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Cusp Hecke prime power
-- statement:
--   The exact prime-power coefficient recurrence, including the exponent-zero boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L218-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L218-L237

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsCuspHecke_prime_power (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (r : ℕ) :
    PowerSeries.coeff (p^(r+1)) (UpperHalfPlane.qExpansion 1 f)=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))-
        if r=0 then 0 else (p:ℂ)*PowerSeries.coeff (p^(r-1)) (UpperHalfPlane.qExpansion 1 f) := by sorry
