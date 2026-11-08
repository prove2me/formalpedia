-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:49:11.205556+00:00
-- url     : https://prove2.me/theorems/ef0df5c6-64cc-4433-8bbc-8dd4cdf246bc
-- title:
--   Tanner Lifted Product: card lps Quaternion Shell eq prime add one
-- statement:
--   The normalized integral quaternion shell used by the LPS construction
--   has exactly `p + 1` elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareCount.lean#L23-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareCount.lean#L23-L27

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionShell p).card = p + 1 := by sorry
