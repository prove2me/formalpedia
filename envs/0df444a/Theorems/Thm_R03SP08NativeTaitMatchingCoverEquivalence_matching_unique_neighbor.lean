-- Prove2me | Theorems.Thm_R03SP08NativeTaitMatchingCoverEquivalence_matching_unique_neighbor
-- name    : R03SP08NativeTaitMatchingCoverEquivalence.matching_unique_neighbor
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:46:54.093759+00:00
-- url     : https://prove2.me/theorems/1b9b6770-de9e-4f34-8053-52f2f6a0ae9e
-- title:
--   R03 P3-factor structural result: matching unique neighbor
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP08NativeTaitMatchingCoverEquivalence.matching_unique_neighbor` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 4b097fd7fcf1d943597114115bcca7972d1a18ba3ea2d2da3881415f140b3b9d.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp08/SP08_NATIVE_TAIT_MATCHING_COVER_EQUIVALENCE_v1.lean; source SHA-256 4b097fd7fcf1d943597114115bcca7972d1a18ba3ea2d2da3881415f140b3b9d; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP08NativeTaitMatchingCoverEquivalence

open R03SP08NativeTaitMatchingCoverEquivalence
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem matching_unique_neighbor
    {G M : SimpleGraph V}
    (hM : CubicP3Partition.PerfectMatching G M)
    {u v w : V} (hv : M.Adj u v) (hw : M.Adj u w) :
    v = w := by sorry

end R03SP08NativeTaitMatchingCoverEquivalence
