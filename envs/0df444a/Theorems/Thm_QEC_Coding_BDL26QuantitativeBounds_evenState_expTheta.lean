-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_expTheta
-- name    : QEC.Coding.BDL26QuantitativeBounds.evenState_expTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:15:43.345579+00:00
-- url     : https://prove2.me/theorems/bf66aa10-9190-4a08-a26e-042dcf7d3108
-- title:
--   BDL26 Quantitative Bounds: even State exp Theta
-- statement:
--   A quantified exp(Theta(k)) statement with positive constants and an explicit start index.
--   Only the upper exponent depends on the one fixed subdivision scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L46-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L46-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.evenState_expTheta (S : OddScale) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : Nat, 1 ≤ k →
      Real.exp ((k : ℝ)*c) ≤ (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤ Real.exp ((k : ℝ)*C) := by sorry
