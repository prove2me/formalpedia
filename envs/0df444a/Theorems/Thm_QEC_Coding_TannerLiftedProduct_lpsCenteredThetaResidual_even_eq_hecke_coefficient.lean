-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_hecke_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_hecke_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:29:32.41247+00:00
-- url     : https://prove2.me/theorems/297f00d2-08ee-4853-82fc-c744e8a582dc
-- title:
--   Tanner Lifted Product: lps Centered Theta Residual even eq hecke coefficient
-- statement:
--   The original centered trace is exactly the true Hecke-action coefficient with the original cardinality and signed term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaHecke.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaHecke.lean#L38-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_hecke_coefficient (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
          (lpsThetaHeckePrimePower p a (2*n)))).re+2*(-(p:ℝ))^n := by sorry
