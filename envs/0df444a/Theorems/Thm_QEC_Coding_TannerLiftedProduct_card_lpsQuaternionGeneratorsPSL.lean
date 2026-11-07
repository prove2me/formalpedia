-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionGeneratorsPSL
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionGeneratorsPSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:45.671554+00:00
-- url     : https://prove2.me/theorems/e4f9cb31-15c2-4f2f-b54e-2529d6ee7bd8
-- title:
--   Tanner Lifted Product: card lps Quaternion Generators PSL
-- statement:
--   Projectivization loses no normalized generators.  The remaining exact
--   degree statement is therefore precisely the cardinality of the integral
--   quaternion shell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L366-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L366-L373

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionGeneratorsPSL
    (a : LPSResiduePrime p) :
    (lpsQuaternionGeneratorsPSL a).card =
      (lpsQuaternionShell p).card := by sorry
