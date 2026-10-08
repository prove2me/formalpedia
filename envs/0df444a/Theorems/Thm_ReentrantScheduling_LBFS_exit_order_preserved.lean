-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_exit_order_preserved
-- name    : ReentrantScheduling.LBFS.exit_order_preserved
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:57.871988+00:00
-- url     : https://prove2.me/theorems/8ba6bc54-9573-4d60-abe4-ed22f941763c
-- title:
--   Proof of Theorem 3, p. 1412 — parts exit the system in the order that they enter it
-- statement:
--   In every LBFS-admissible run of a nonacyclic flow line, parts exit the system in the order in which they entered it: if part $p$ precedes part $q$ in line order, then
--
--   $$
--   e(p) \le e(q).
--   $$
--
--   The line order lists the parts present at time $0$ first, deeper buffers first, and the released parts by release time, ties broken by a fixed order that the head-of-buffer rule respects. The fact is used in the proof of Theorem 3 to identify the parts in the system at an exit time with the parts that arrived since the previous one.
--
--   **Formalization Note.** Exit times are in `WithTop ℝ`: if $p$ is never served, neither is $q$.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1412, proof of Theorem 3

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- Proof of Theorem 3, p. 1412: under LBFS, parts exit the system in the order that they
enter it (line order `ord`). -/
theorem exit_order_preserved (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (p q : R.Part) (hpq : R.ord p < R.ord q) : R.exit p ≤ R.exit q := by sorry

end ReentrantScheduling.LBFS
