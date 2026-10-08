-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_long_odd_prism_decomposition
-- name    : StrongPerfectGraph.OddPrism.long_odd_prism_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:10:06.963063+00:00
-- url     : https://prove2.me/theorems/2e6bf2db-f4dc-4d4e-9fe6-fd15f18271f1
-- title:
--   13.4, p. 152 — a Berge graph containing a long odd prism decomposes (step 1.8.5)
-- statement:
--   Let $G$ be a Berge graph such that there is no appearance of $K_4$ in either $G$ or $\overline{G}$. Suppose that $G$ contains a long odd prism as an induced subgraph. Then
--   $$\text{one of } G,\ \overline{G} \text{ admits a proper 2-join, or } G \text{ admits a balanced skew partition, or } G \text{ admits a proper homogeneous pair.}$$
--
--   This is step 1.8.5 of the proof of the strong perfect graph theorem: after it, every recalcitrant graph contains no long prism in $G$ or $\overline{G}$. It is the only place in the paper where proper homogeneous pairs are needed.
--
--   **Formalization Note** "No appearance of $K_4$" excludes all appearances, degenerate or not; "long odd prism" is a prism with some path of length $>1$ whose three path lengths are not all even.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 152, 13.4 (= 1.8.5, p. 59)

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_Main_IsProperHomogeneousPair

namespace StrongPerfectGraph.OddPrism

/-- **13.4** (p. 152; step 1.8.5). Let `G` be Berge, such that there is no appearance of `K₄`
in either `G` or its complement. Suppose that `G` contains a long odd prism as an induced
subgraph. Then either one of `G`, `Gᶜ` admits a proper 2-join, or `G` admits a balanced skew
partition, or `G` admits a proper homogeneous pair. -/
theorem long_odd_prism_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G)
    (hK4 : ¬ AppearsIn K4 G) (hK4c : ¬ AppearsIn K4 Gᶜ)
    (hprism : ContainsLongOddPrism G) :
    StrongPerfectGraph.Main.IsProperTwoJoin G ∨ StrongPerfectGraph.Main.IsProperTwoJoin Gᶜ ∨ StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G ∨
      StrongPerfectGraph.Main.IsProperHomogeneousPair G := by sorry

end StrongPerfectGraph.OddPrism
