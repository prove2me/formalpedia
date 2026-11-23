-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleWindows_singleton_grammar_exact_window_partitions
-- name    : StableMSR.Recovery.SingleWindows.singleton_grammar_exact_window_partitions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:03:17.107713+00:00
-- url     : https://prove2.me/theorems/bf452bd2-91ff-4e0a-8560-31bacde95f3f
-- title:
--   Projecting singleton separator assignments gives exactly the admissible owned window partitions
-- statement:
--   Specializing the constraint domains to the actual ball-trace menus and projecting owned blocks gives an exact set equality. Every admissible window partition is recovered, including tied choices.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleWindowGrammar
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

theorem StableMSR.Recovery.SingleWindows.singleton_grammar_exact_window_partitions (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (Q : Partition x.n) :
    generates x W R h w Q ↔ TreewidthLE (interactionGraph x.dist R W) w ∧
      ∃P : Pick x.n,valid x W R h P ∧ WindowCSP.output x W R P=Q := by sorry
