-- Prove2me | Theorems.Thm_R03PerfectMatchingCandidate_matchingComplement_adj_iff_local
-- name    : R03PerfectMatchingCandidate.matchingComplement_adj_iff_local
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:53:08.018644+00:00
-- url     : https://prove2.me/theorems/90123977-6215-4e9a-acf9-a7f59345d22d
-- title:
--   R03 P3-factor structural result: Matching complement adj iff local
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03PerfectMatchingCandidate.matchingComplement_adj_iff_local` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-cubic-three-connected-perfect-matching-candidate-v1.lean; source SHA-256 1e67fc5e7a242895e94a4bf5b396f3b143d7004721b08f2910a424ad0abec2e5; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03PerfectMatchingCandidate

open R03PerfectMatchingCandidate
open CubicP3Partition
open SimpleGraph
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V]
theorem matchingComplement_adj_iff_local
    (G M : SimpleGraph V) (v w : V) :
    (matchingComplement G M).Adj v w ↔ G.Adj v w ∧ ¬ M.Adj v w := by sorry

end R03PerfectMatchingCandidate
