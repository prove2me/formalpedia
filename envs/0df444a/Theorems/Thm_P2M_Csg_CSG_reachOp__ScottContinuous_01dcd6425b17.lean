-- Prove2me | Theorems.Thm_P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17
-- name    : P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:16:55.07818+00:00
-- url     : https://prove2.me/theorems/50a6bbc1-41a5-48e3-adc6-cbd943a3e9a4
-- title:
--   P2 M Csg CSG reach Op  Scott Continuous 01dcd6425b17: P2 M Csg CSG reach Op  Scott Continuous 01dcd6425b17
-- statement:
--   **The payoff.** The reachability Bellman operator is `ωScottContinuous`: applying it to a
--       chain's supremum gives the same answer as taking the supremum of applying it along the chain.
--       Exactly Kleene's fixed-point theorem's hypothesis (`fixedPoints.lfp_eq_sSup_iterate`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L108-L173
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L108-L173

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge
set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17 (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    ωScottContinuous (C.reachOp goal hr) := by sorry

alias «Csg».«CSG».«reachOp_ωScottContinuous» := P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17
