-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsGeneratorSum_pow_one
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsGeneratorSum_pow_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:21:54.215822+00:00
-- url     : https://prove2.me/theorems/dbfbf767-4c71-45fa-a7db-63efb87f39ce
-- title:
--   Tanner Lifted Product: coeff lps Generator Sum pow one
-- statement:
--   The identity coefficient of the ordinary LPS adjacency power is the
--   number of closed labelled words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L144-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L144-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsGeneratorSum_pow_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (cayleyGeneratorSum (lpsQuaternionLabel a) ^ n).coeff 1 =
      ((lpsClosedWords a n).card : ℂ) := by sorry
