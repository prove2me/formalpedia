-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleCodes_finite_ball_word_menu_exact
-- name    : StableMSR.Recovery.SingleCodes.finite_ball_word_menu_exact
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T00:08:30.398253+00:00
-- url     : https://prove2.me/theorems/e9c3533f-c01a-4753-b2d6-8e95a2c164e4
-- title:
--   Integer ball words enumerate precisely the mission window menu
-- statement:
--   One nonnegative integer names a trace index and Cartesian ball tuple. After the feasibility test, decoding those integers gives exactly the existing window menu, including duplicate encodings or an empty window.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleWindowCodes
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleCodes StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows

theorem StableMSR.Recovery.SingleCodes.finite_ball_word_menu_exact (x : World) (W : Cluster x.n) (h : ℕ) (P : Partition x.n) :
    P∈traceMenu x h W ↔ ∃c∈SingleCodes.menu x W h,SingleCodes.decode x W h c=P := by sorry
