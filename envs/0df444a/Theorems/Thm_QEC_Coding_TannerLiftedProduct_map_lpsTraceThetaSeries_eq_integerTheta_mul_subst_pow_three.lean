-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_map_lpsTraceThetaSeries_eq_integerTheta_mul_subst_pow_three
-- name    : QEC.Coding.TannerLiftedProduct.map_lpsTraceThetaSeries_eq_integerTheta_mul_subst_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:38:50.136325+00:00
-- url     : https://prove2.me/theorems/674f3b5e-4d6c-4b85-9ad8-030ad7074338
-- title:
--   Tanner Lifted Product: map lps Trace Theta Series eq integer Theta mul subst pow three
-- statement:
--   Integral-coefficient substitution form of the diagonal factorization.
--   This is the standard theta-product expression used to establish modularity
--   of the trace series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L278-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L278-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.map_lpsTraceThetaSeries_eq_integerTheta_mul_subst_pow_three
    {q : ℕ} (hq : 0 < q) :
    (lpsTraceThetaSeries q).map (Nat.castRingHom ℤ) =
      integerThetaSeries.map (Nat.castRingHom ℤ) *
        (PowerSeries.subst
          (PowerSeries.X ^ ((2 * q) ^ 2))
          (integerThetaSeries.map (Nat.castRingHom ℤ))) ^ 3 := by sorry
