-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_pure_power_bounds
-- name    : QEC.Coding.BDL26QuantitativeBounds.evenState_pure_power_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:16:27.6245+00:00
-- url     : https://prove2.me/theorems/897b56fd-4e7e-4613-9019-06dc708c2ac1
-- title:
--   BDL26 Quantitative Bounds: even State pure power bounds
-- statement:
--   Absorb the finite prefactors at positive even depths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L11-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean#L11-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.evenState_pure_power_bounds (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    4 ^ k ≤ Fintype.card (state S (2*k)).presentation.Q ∧
      Fintype.card (state S (2*k)).presentation.Q ≤ evenGrowthEnvelope S ^ k := by sorry
