-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCRT_linear_bijective
-- name    : QEC.Coding.TannerLiftedProduct.lpsCRT_linear_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:47:45.798628+00:00
-- url     : https://prove2.me/theorems/f5d2ea67-bbb3-4ae9-885a-ac50add5de62
-- title:
--   Tanner Lifted Product: lps CRT linear bijective
-- statement:
--   The actual linear CRT parametrization is bijective by unit cancellation and cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L78-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean#L78-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex

theorem QEC.Coding.TannerLiftedProduct.lpsCRT_linear_bijective (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    Function.Bijective (fun r : Fin m × Fin n =>
      ((n*r.1.val+m*r.2.val:ℕ):ZMod (m*n))) := by sorry
