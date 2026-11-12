-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_no_uniform_singleton_bound
-- name    : QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.no_uniform_singleton_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:25:15.027882+00:00
-- url     : https://prove2.me/theorems/fd29c52b-ac2a-4837-8874-11ef544e4c33
-- title:
--   BDL26 RXIncidence Hull Retained Growth: no uniform singleton bound
-- statement:
--   At EVERY fixed legal odd scale, singleton hulls exceed every proposed
--   depth-independent cardinal bound already at legal even-source RX steps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L154-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean#L154-L165

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

theorem QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.no_uniform_singleton_bound (S : OddScale) (C : Nat) :
    ∃ (depth : Nat) (i : StepIndex depth), i.val % 2 = 0 ∧
      (seed S i.val).card = 1 ∧ C < (incidenceHull S depth i (seed S i.val)).card := by sorry
