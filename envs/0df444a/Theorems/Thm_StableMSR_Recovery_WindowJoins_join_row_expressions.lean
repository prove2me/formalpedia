-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_join_row_expressions
-- name    : StableMSR.Recovery.WindowJoins.join_row_expressions
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:37:50.074407+00:00
-- url     : https://prove2.me/theorems/9ed50c28-94ec-4091-8afd-b1c437a071dd
-- title:
--   Bounded oracle expressions implement leaf data, binary joins, and minimum comparisons
-- statement:
--   All three synchronized passes are bounded expressions over the distance oracle. Candidate words are indexed with bounded shifted slots, priced using sums of oracle answers, and compared exactly before the selected center and radius witness are emitted.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowJoins.join_row_expressions : (∀w : Bool,Form (fun x ρ=>iv (seed x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (advance x (ρ 0) (ρ 1) w))) ∧
    (∀w : Bool,Form (fun x ρ=>iv (project x (ρ 0) (ρ 1) w))) ∧ Form (fun x _=>iv (storedScenes x)) := by sorry
