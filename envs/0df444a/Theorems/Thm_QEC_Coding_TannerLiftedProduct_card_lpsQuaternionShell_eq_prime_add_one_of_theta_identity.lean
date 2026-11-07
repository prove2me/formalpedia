-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:53.344472+00:00
-- url     : https://prove2.me/theorems/4f9b048e-fdef-41a0-93d8-fe2417c24711
-- title:
--   Tanner Lifted Product: card lps Quaternion Shell eq prime add one of theta identity
-- statement:
--   The same standard theta identity supplies the exact normalized LPS
--   generator count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L267-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L267-L272

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionShell p).card = p + 1 := by sorry
