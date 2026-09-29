-- Prove2me | Theorems.Thm_R03FixedPerfectMatchingBridge_p3Path_iff_intervalTile
-- name    : R03FixedPerfectMatchingBridge.p3Path_iff_intervalTile
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:23:11.361997+00:00
-- url     : https://prove2.me/theorems/39879b90-5cce-459a-9c74-8b1e1e6d3986
-- title:
--   R03 P3-factor structural result: P3 path iff interval tile
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03FixedPerfectMatchingBridge.p3Path_iff_intervalTile` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/w64_fixed_perfect_matching_bridge_v1.lean; source SHA-256 fa69158672a2394546661234b7751ee4c84f4faef502f65cda0085ea91e51524; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1

namespace R03FixedPerfectMatchingBridge

open R03FixedPerfectMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem p3Path_iff_intervalTile
    (G M : SimpleGraph V)
    (hMsub : M ≤ G)
    (hMmatch : IsMatchingRelation M)
    {a b c : V} :
    P3PathProp G a b c ↔ IntervalTile G M a b c := by sorry

end R03FixedPerfectMatchingBridge
