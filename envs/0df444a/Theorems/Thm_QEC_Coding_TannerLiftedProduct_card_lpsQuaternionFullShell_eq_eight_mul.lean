-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_eight_mul
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:34:54.072659+00:00
-- url     : https://prove2.me/theorems/2b88305f-63af-44fa-9127-f991589c8ab0
-- title:
--   Tanner Lifted Product: card lps Quaternion Full Shell eq eight mul
-- statement:
--   The full ordered signed four-square shell has exactly eight times as many
--   elements as the normalized LPS shell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionCount.lean#L331-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionCount.lean#L331-L341

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Mathlib.NumberTheory.Multiplicity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul
    (hp : 0 < p) (hp4 : p % 4 = 1) :
    (lpsQuaternionFullShell p).card =
      8 * (lpsQuaternionShell p).card := by sorry
