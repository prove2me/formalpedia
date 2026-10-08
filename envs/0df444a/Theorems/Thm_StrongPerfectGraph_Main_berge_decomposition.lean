-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_berge_decomposition
-- name    : StrongPerfectGraph.Main.berge_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:59:58.904785+00:00
-- url     : https://prove2.me/theorems/d89a8f20-9978-4dcb-9b40-54fc8fa33452
-- title:
--   1.3 — decomposition of Berge graphs
-- statement:
--   Let $G$ be a finite Berge graph. Then at least one of the following holds:
--
--   1. $G$ is basic;
--   2. $G$ or $\overline G$ admits a proper 2-join;
--   3. $G$ admits a proper homogeneous pair;
--   4. $G$ admits a balanced skew partition.
--
--   $$\operatorname{Berge}(G)\Longrightarrow\operatorname{Basic}(G)\lor\operatorname{TwoJoin}(G)\lor\operatorname{TwoJoin}(\overline G)\lor\operatorname{HomPair}(G)\lor\operatorname{BalancedSkew}(G).$$
--
--   The asymmetry is deliberate: the complement appears in the 2-join alternative, while the homogeneous-pair and balanced-skew alternatives concern $G$. This is the structural result from which the paper derives its main theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 54, 1.3

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_Main_IsProperHomogeneousPair
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.Main

/-- The decomposition theorem, Theorem 1.3. -/
theorem berge_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBerge G) :
    IsBasic G ∨ IsProperTwoJoin G ∨ IsProperTwoJoin Gᶜ ∨
      IsProperHomogeneousPair G ∨ AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.Main
