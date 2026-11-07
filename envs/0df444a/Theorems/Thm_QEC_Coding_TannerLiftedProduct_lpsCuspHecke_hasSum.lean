-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHecke_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHecke_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:12.598484+00:00
-- url     : https://prove2.me/theorems/3870e4dc-4145-42f3-addd-6b7b7ca5148a
-- title:
--   Tanner Lifted Product: lps Cusp Hecke has Sum
-- statement:
--   The exact coefficient formula gives a convergent expansion of the actual operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L166-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L166-L175

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHecke_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)+
      (p:ℂ)*lpsModularDilationCoefficient
        (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n)*
          Function.Periodic.qParam 1 (z:ℂ)^n) (lpsCuspHecke N p hNp f z) := by sorry
