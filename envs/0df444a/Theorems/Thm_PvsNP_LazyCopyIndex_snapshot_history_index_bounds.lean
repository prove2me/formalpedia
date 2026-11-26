-- Prove2me | Theorems.Thm_PvsNP_LazyCopyIndex_snapshot_history_index_bounds
-- name    : PvsNP.LazyCopyIndex.snapshot_history_index_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:18:59.540801+00:00
-- url     : https://prove2.me/theorems/5f67489f-146f-463a-867a-08092136b901
-- title:
--   Exact source recovery and operation bounds for indexed snapshot histories
-- statement:
--   Consider a history of $p$ operations on a tape of integer-valued source labels. An operation either assigns labels given by an affine function of the destination address on a half-open interval, or copies labels from a source range as they were before that operation. Source and destination ranges may overlap. The history is stored newest first. Form the sorted set of all target interval endpoints and let $d$ be the bit length of its size. Build a persistent interval index that stores the last writer at every version. To recover the current label at an address, use the index to find its last writer and, for a copy, continue at the corresponding source address in the preceding version.
--
--   The index returns the same label as eager evaluation for every initial labeling and address. With the sorted endpoints supplied, building the index uses at most $(6d+1)p$ counted endpoint comparisons and tree-node visits in total. A query uses at most $2d+1$ of these counted operations per last-writer lookup and makes at most $p+1$ such lookups. There are at most $2p$ distinct endpoints.
-- source:
--   Original Prove2Me P vs NP exploration formalization. Main theorem PvsNP.LazyCopyIndex.recoverFast_from_original in PvsNPIndexedSnapshotFast.lean, with the separate endpoint bound PvsNP.SourceIntervalMap.boundaries_card in PvsNPSourceIntervalMap.lean. This is a standalone result for an interval-history data structure.

import Definitions.Def_PvsNP_SnapshotHistoryIndex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size

open PvsNP.LazyCopyIndex PvsNP.SourceIntervalMap

theorem PvsNP.LazyCopyIndex.snapshot_history_index_bounds (history : List Instruction) (initial : Origins) (address : ℕ) :
    let cuts := cutsOf history
    let keys := cuts.sort.toArray
    let depth := cuts.card.size
    let table := buildFast keys depth history
    let result := resolveFast table.1 keys initial history.length address
    result.origin = eval history initial address ∧
      table.2 ≤ (6*depth+1)*history.length ∧
      result.nodeVisits ≤ (2*depth+1)*result.probes ∧
      result.probes ≤ history.length+1 ∧
      cuts.card ≤ 2*history.length := by sorry
