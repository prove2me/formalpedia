-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_partitionYes_filter_reverse
-- name    : ProjSchedTW.Complexity.partitionYes_filter_reverse
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T23:34:53.37957+00:00
-- url     : https://prove2.me/theorems/e61a4f23-413f-4f12-ad93-4eacf1448b04
-- title:
--   Removing zeros and reversing preserves PARTITION
-- statement:
--   For any finite list of natural numbers, deleting all zero entries and reversing the remaining list preserves whether its indexed entries admit a partition into two equal sums. Zero entries contribute nothing, and reversal only relabels the indices. This is the preprocessing invariant needed by the binary encoding reduction to the two-agent scheduling problem.
-- source:
--   Supporting preprocessing lemma for the ProjSchedTW.Complexity PARTITION language and the two-agent scheduling encoding reduction.

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
open ProjSchedTW.Complexity

theorem ProjSchedTW.Complexity.partitionYes_filter_reverse (xs : List ℕ) :
    PartitionYes xs ↔ PartitionYes ((xs.filter (fun a => a ≠ 0)).reverse) := by sorry
