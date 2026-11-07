-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_map_scaledIntegerThetaSeries_eq_subst
-- name    : QEC.Coding.TannerLiftedProduct.map_scaledIntegerThetaSeries_eq_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:38:27.1342+00:00
-- url     : https://prove2.me/theorems/e7b61647-5c19-42bc-a475-490da0f230e5
-- title:
--   Tanner Lifted Product: map scaled Integer Theta Series eq subst
-- statement:
--   After extending coefficients to the integers, scaling the variable in
--   the unary theta series by `m` is formal substitution `X ↦ X^(m²)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L98-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L98-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.map_scaledIntegerThetaSeries_eq_subst
    {m : ℕ} (hm : 0 < m) :
    (scaledIntegerThetaSeries m).map (Nat.castRingHom ℤ) =
      PowerSeries.subst (PowerSeries.X ^ (m ^ 2))
        (integerThetaSeries.map (Nat.castRingHom ℤ)) := by sorry
