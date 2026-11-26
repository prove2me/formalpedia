-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_native_window_join_records
-- name    : StableMSR.Recovery.WindowJoins.native_window_join_records
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:37:58.981833+00:00
-- url     : https://prove2.me/theorems/058fddd8-64f6-46c8-9d8c-5b73bde7dd9a
-- title:
--   Construct the unoptimized leaf and binary-join records for the bounded-width regional window problems
-- statement:
--   Produce an acyclic table of literal window witnesses and permissible binary joins, with one designated output state for each scenario, region, and count. Derivations at that state must cover the region, and every compatible assignment must be representable at no greater cost. The generator can enumerate all locally compatible alternatives and does not have to identify winning alternatives or reconstruct an optimal regional witness.
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

theorem StableMSR.Recovery.WindowJoins.native_window_join_records : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,buildSpec e c D b cmd := by sorry
