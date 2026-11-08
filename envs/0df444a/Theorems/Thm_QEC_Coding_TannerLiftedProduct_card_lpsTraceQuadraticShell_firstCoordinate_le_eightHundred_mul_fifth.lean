-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:36.17527+00:00
-- url     : https://prove2.me/theorems/32e57bfd-f6fe-47ee-a640-32d25665371a
-- title:
--   Tanner Lifted Product: card lps Trace Quadratic Shell first Coordinate le eight Hundred mul fifth
-- statement:
--   The Tanner Lifted Product construction uses the card lps Trace Quadratic Shell first Coordinate le eight Hundred mul fifth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L136-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L136-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth
    (q n K : ℕ) (hq : 0 < q) (hK : 0 < K) (hn : n ≤ 4*q^2*K^6) (x : ℤ) :
    ((lpsTraceQuadraticShell q n).filter fun t => t.a=x).card ≤ 800*K^5 := by sorry
