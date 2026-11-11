-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_singleton_hull_card_lower
-- name    : QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.singleton_hull_card_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:21:13.586043+00:00
-- url     : https://prove2.me/theorems/e10e8399-f278-4d22-9e4d-c3f74a0a6b39
-- title:
--   BDL26 RXIncidence Hull Retained Growth: singleton hull card lower
-- statement:
--   The original singleton hull contains all five times two-to-the-level
--   retained coordinates. This is an ACTUAL hull bound, not a global Q count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L128-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L128-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks

theorem QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.singleton_hull_card_lower (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    5*2^i.val ≤ (incidenceHull S depth i (seed S i.val)).card := by sorry
