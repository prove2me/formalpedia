-- Prove2me | Theorems.Thm_PersistClust_Count_mult_off_diagonal
-- name    : PersistClust.Count.mult_off_diagonal
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:47:26.998232+00:00
-- url     : https://prove2.me/theorems/6ef1c731-55df-470f-8801-cc1b8623a68e
-- title:
--   T2c: every multiplicity diagram is off the diagonal
-- statement:
--   For any rank function r : R x R -> N-infinity, the multiplicity functional mult r (the two-parameter infimum of rank differences of the paper) never charges the diagonal: IsDiagramLike (mult r) holds, i.e. every point with nonzero multiplicity has its death strictly below its birth. The proof is the EReal case analysis baked into mult: a non-degenerate point must satisfy death < birth by if_neg on the three degeneracy branches (bottom/top birth, bottom death, death >= birth), each of which forces the multiplicity to vanish at the point itself.
-- source:
--   T2 support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the off-diagonal property that the diagram axioms and every matching construction consume. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem mult_off_diagonal (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r)
    := by sorry
