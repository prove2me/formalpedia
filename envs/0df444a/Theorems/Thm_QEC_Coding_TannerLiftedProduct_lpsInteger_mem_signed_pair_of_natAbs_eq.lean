-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsInteger_mem_signed_pair_of_natAbs_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsInteger_mem_signed_pair_of_natAbs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:21.149915+00:00
-- url     : https://prove2.me/theorems/721777f9-d744-4132-9f3b-bda4dc125fac
-- title:
--   Tanner Lifted Product: lps Integer mem signed pair of nat Abs eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer mem signed pair of nat Abs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L342-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L342-L351

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsInteger_mem_signed_pair_of_natAbs_eq (x : ℤ) (n : ℕ) (h : x.natAbs=n) :
    x ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ) := by sorry
