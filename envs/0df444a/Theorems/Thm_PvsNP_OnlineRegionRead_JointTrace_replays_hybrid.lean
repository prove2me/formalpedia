-- Prove2me | Theorems.Thm_PvsNP_OnlineRegionRead_JointTrace_replays_hybrid
-- name    : PvsNP.OnlineRegionRead.JointTrace.replays_hybrid
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:24:34.351389+00:00
-- url     : https://prove2.me/theorems/249460c4-5df1-5d5c-9271-42fe8fe708a1
-- title:
--   Aligned regional traces permit one-way input splicing
-- statement:
--   Given a regional certificate for two traces, the machine has a run on the hybrid input selected by the certified routing. The final state, work-head position and input position are those of the first trace, and the resulting tape combines the two final tape regions.
-- source:
--   Regional replay step in the crossing-sequence method of Kalyanasundaram and Schnitger (DOI 10.1007/978-3-322-95233-2_15).

import Definitions.Def_OnlineRegionalTrace
set_option autoImplicit false

open PvsNP.OnlineRegionRead

theorem PvsNP.OnlineRegionRead.JointTrace.replays_hybrid
    {Q Γ : Type} {M : Program Q Γ} {one zero : Word} {route : ℕ → Bool}
    {before after : ℤ → Bool} {a a' b b' : Cursor Q Γ}
    (trace : JointTrace M one zero route before a b after a' b') :
    ∃ k, Run M (hybridWord route one zero) (merge before true a b) (merge after true a' b') k := by sorry
