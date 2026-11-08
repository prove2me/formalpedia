-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:57:03.751342+00:00
-- url     : https://prove2.me/theorems/15f0f09b-04b3-4c62-b899-445e520ae7c5
-- title:
--   Tanner Lifted Product: card lps Quaternion Full Shell eq prime
-- statement:
--   A prime congruent to one modulo four has exactly `8 (p + 1)` ordered,
--   signed integral four-square representations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareCount.lean#L15-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareCount.lean#L15-L19

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) := by sorry
