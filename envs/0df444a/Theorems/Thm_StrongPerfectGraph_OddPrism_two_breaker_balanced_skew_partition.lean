-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_two_breaker_balanced_skew_partition
-- name    : StrongPerfectGraph.OddPrism.two_breaker_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:53:15.789685+00:00
-- url     : https://prove2.me/theorems/6ceb239d-a022-4d71-9a60-ab3cea718a1d
-- title:
--   12.4, p. 140 — a 2-breaker forces a balanced skew partition
-- statement:
--   Let $G$ be a Berge graph containing no appearance of $K_4$, no even prism and no 1-breaker. If there is a 2-breaker in $G$, then
--   $$G \text{ admits a balanced skew partition.}$$
--
--   In particular, under these hypotheses a strongly maximal staircase has no central vertex unless $G$ admits a balanced skew partition.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 140, 12.4

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker
import Definitions.Def_StrongPerfectGraph_OddPrism_IsTwoBreaker
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.OddPrism

/-- **12.4** (p. 140). Let `G` be a Berge graph containing no appearance of `K₄`, no even prism
and no 1-breaker. If there is a 2-breaker in `G` then `G` admits a balanced skew
partition. -/
theorem two_breaker_balanced_skew_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G) (h1 : ¬ HasOneBreaker G) (h2 : HasTwoBreaker G) :
    StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.OddPrism
