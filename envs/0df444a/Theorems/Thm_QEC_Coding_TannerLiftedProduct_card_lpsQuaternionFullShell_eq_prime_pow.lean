-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime_pow
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:05.382655+00:00
-- url     : https://prove2.me/theorems/7934b7a4-e8db-4adb-94d4-0535d3eacf42
-- title:
--   Tanner Lifted Product: card lps Quaternion Full Shell eq prime pow
-- statement:
--   Exact four-square count at every prime power used in the LPS
--   factorization argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L48-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L48-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_prime_pow
    (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    (lpsQuaternionFullShell (p ^ k)).card =
      8 * ∑ i ∈ Finset.range (k + 1), p ^ i := by sorry
