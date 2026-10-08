-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_perfect_iff_berge
-- name    : StrongPerfectGraph.Main.perfect_iff_berge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:38:08.197871+00:00
-- url     : https://prove2.me/theorems/3cb914ca-feaf-4b61-888f-4d4cad21c705
-- title:
--   1.2 — strong perfect graph theorem
-- statement:
--   For every finite simple graph $G$, perfection is equivalent to the Berge property:
--
--   $$G\text{ is perfect}\quad\Longleftrightarrow\quad G\text{ is Berge}.$$
--
--   Perfection requires $\chi(H)=\omega(H)$ for every induced subgraph $H$ of $G$. The Berge property requires every induced cycle of length at least four in $G$ and $\overline G$ to have even length. This is the main theorem of the paper and closes Berge’s strong perfect graph conjecture.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 52, 1.2

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- The strong perfect graph theorem, Theorem 1.2. -/
theorem perfect_iff_berge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsPerfect G ↔ IsBerge G := by sorry

end StrongPerfectGraph.Main
