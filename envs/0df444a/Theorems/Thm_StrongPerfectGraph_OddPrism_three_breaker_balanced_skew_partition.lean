-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_three_breaker_balanced_skew_partition
-- name    : StrongPerfectGraph.OddPrism.three_breaker_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:53:18.143006+00:00
-- url     : https://prove2.me/theorems/b6aa1f7e-ffc7-4482-9194-9c09dcb8df61
-- title:
--   13.3, p. 151 — a 3-breaker forces a balanced skew partition
-- statement:
--   Let $G$ be a Berge graph containing no appearance of $K_4$, no even prism, no 1-breaker and no 2-breaker. If there is a 3-breaker in $G$, then
--   $$G \text{ admits a balanced skew partition.}$$
--
--   This is the last of the three breaker results used in the proof of 13.4.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 151, 13.3

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker
import Definitions.Def_StrongPerfectGraph_OddPrism_IsTwoBreaker
import Definitions.Def_StrongPerfectGraph_OddPrism_IsThreeBreaker
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.OddPrism

/-- **13.3** (p. 151). Let `G` be Berge, containing no appearance of `K₄`, no even prism, no
1-breaker and no 2-breaker. If there is a 3-breaker in `G` then `G` admits a balanced skew
partition. -/
theorem three_breaker_balanced_skew_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) (hK4 : ¬ AppearsIn K4 G)
    (hprism : ¬ ContainsEvenPrism G) (h1 : ¬ HasOneBreaker G) (h2 : ¬ HasTwoBreaker G)
    (h3 : HasThreeBreaker G) :
    StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.OddPrism
