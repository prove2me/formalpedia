-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_one_breaker_balanced_skew_partition
-- name    : StrongPerfectGraph.OddPrism.one_breaker_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:52:43.052268+00:00
-- url     : https://prove2.me/theorems/1a7ec827-8cd3-4010-9476-7a62f2070ac4
-- title:
--   11.5, p. 131 — a 1-breaker forces a balanced skew partition
-- statement:
--   Let $G$ be a Berge graph such that there is no appearance of $K_4$ in $G$ and no even prism in $G$. If there is a 1-breaker in $G$, then
--   $$G \text{ admits a balanced skew partition.}$$
--
--   Together with 12.4 and 13.3 this removes the three kinds of breaker from the analysis of a long odd prism.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 131, 11.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.OddPrism

/-- **11.5** (p. 131). Let `G` be a Berge graph with no appearance of `K₄` and no even prism.
If there is a 1-breaker in `G` then `G` admits a balanced skew partition. -/
theorem one_breaker_balanced_skew_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G) (h1 : HasOneBreaker G) :
    StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.OddPrism
