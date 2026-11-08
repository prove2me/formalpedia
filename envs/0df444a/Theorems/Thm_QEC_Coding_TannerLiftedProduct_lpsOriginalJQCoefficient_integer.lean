-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_integer
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJQCoefficient_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:21:52.876745+00:00
-- url     : https://prove2.me/theorems/42076e9e-b625-4e19-8137-dcc942162acc
-- title:
--   Tanner Lifted Product: lps Original JQCoefficient integer
-- statement:
--   Every genuine Taylor coefficient of SAME original K is an actual integer cast; no supplied coefficient law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L207-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L207-L211

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJQCoefficient_integer (n : ℕ) :
    ∃ a : ℤ,(a:ℂ)=(n.factorial:ℂ)⁻¹*iteratedDeriv n lpsOriginalJQCoefficient 0 := by sorry
