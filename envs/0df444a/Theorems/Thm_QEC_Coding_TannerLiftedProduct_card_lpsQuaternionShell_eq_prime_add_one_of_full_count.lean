-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one_of_full_count
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_full_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:34:50.90161+00:00
-- url     : https://prove2.me/theorems/1e73b5dc-ed10-456c-a033-ef90663ff25e
-- title:
--   Tanner Lifted Product: card lps Quaternion Shell eq prime add one of full count
-- statement:
--   Jacobi's prime four-square count immediately gives the desired `p+1`
--   normalized generators.  This theorem isolates the sole remaining arithmetic
--   input as a statement about the standard full representation shell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionCount.lean#L346-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionCount.lean#L346-L351

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Mathlib.NumberTheory.Multiplicity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_full_count
    (hp : 0 < p) (hp4 : p % 4 = 1)
    (hFull : (lpsQuaternionFullShell p).card = 8 * (p + 1)) :
    (lpsQuaternionShell p).card = p + 1 := by sorry
