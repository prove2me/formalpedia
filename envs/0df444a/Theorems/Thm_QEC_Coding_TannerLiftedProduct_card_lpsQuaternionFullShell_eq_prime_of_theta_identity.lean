-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime_of_theta_identity
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_of_theta_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:50.52033+00:00
-- url     : https://prove2.me/theorems/e3c12486-52db-4c64-9e09-4081288b47b2
-- title:
--   Tanner Lifted Product: card lps Quaternion Full Shell eq prime of theta identity
-- statement:
--   Jacobi's formal theta identity implies the exact prime full-shell count.
--   This pins the remaining arithmetic theorem to one standard power-series
--   identity, with the combinatorial and prime-specialization steps discharged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L257-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L257-L263

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_of_theta_identity
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) := by sorry
