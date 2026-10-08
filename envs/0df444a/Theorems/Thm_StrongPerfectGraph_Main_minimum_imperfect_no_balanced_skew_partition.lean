-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_balanced_skew_partition
-- name    : StrongPerfectGraph.Main.minimum_imperfect_no_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:59:12.762368+00:00
-- url     : https://prove2.me/theorems/8daa10d8-62ca-4a35-9974-8f553e7328fc
-- title:
--   1.5 — no balanced skew partition in a minimum imperfect graph
-- statement:
--   Let $G$ be a minimum imperfect graph: $G$ is Berge and not perfect, and no smaller Berge graph is imperfect. Then $G$ has no balanced skew partition:
--
--   $$\operatorname{MinimumImperfect}(G)\quad\Longrightarrow\quad\neg\operatorname{AdmitsBalancedSkewPartition}(G).$$
--
--   Balanced skew partitions require the two parity restrictions on induced paths and antipaths. This lemma removes the skew-partition outcome from a hypothetical minimum counterexample to 1.2.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 55, 1.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsMinimumImperfect
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.Main

/-- A minimum imperfect graph has no balanced skew partition, Theorem 1.5. -/
theorem minimum_imperfect_no_balanced_skew_partition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsMinimumImperfect G) : ¬ AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.Main
