-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_exponential_bounds
-- name    : QEC.Coding.BDL26QuantitativeBounds.evenState_exponential_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:16:54.707436+00:00
-- url     : https://prove2.me/theorems/d7c60ade-db60-4efa-8110-89317c85ecc3
-- title:
--   BDL26 Quantitative Bounds: even State exponential bounds
-- statement:
--   Explicit real exponential bounds for the source n_(2k) relation, for fixed ell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L27-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L27-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.evenState_exponential_bounds (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    Real.exp ((k : ℝ) * Real.log 4) ≤
        (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤
        Real.exp ((k : ℝ) * Real.log (evenGrowthEnvelope S : ℝ)) := by sorry
