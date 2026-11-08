-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_perfect_berge
-- name    : StrongPerfectGraph.Main.perfect_berge
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T06:14:45.553921+00:00
-- url     : https://prove2.me/theorems/e60ba857-9e14-4854-a0a8-3bc86ca0a8d9
-- title:
--   Every perfect graph is Berge
-- statement:
--   Let $G$ be a finite simple graph. Call $G$ *perfect* if $\chi(H)=\omega(H)$ for every induced subgraph $H$ of $G$, and *Berge* if every hole (induced cycle of length at least $4$) of $G$ and of its complement $\overline G$ has even length. Then
--
--   $$G\ \text{perfect}\ \Longrightarrow\ G\ \text{Berge}.$$
--
--   This is the easy direction of the strong perfect graph theorem, recorded in the paper's introduction ("Since every perfect graph is Berge, to prove 1.2 it remains to prove the converse"). An odd hole $C_{2k+1}$, $k\ge 2$, has clique number $2$ but chromatic number $3$; an odd antihole is handled through Lovász's theorem 1.1 (the complement of a perfect graph is perfect).
--
--   **Formalization Note** Perfection and the Berge property are the mission definitions `IsPerfect` and `IsBerge`; holes are cyclically listed vertex lists (`IsHole`).
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 52 (paragraph following Theorem 1.2: "every perfect graph is Berge")

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- Every perfect graph is Berge (the easy direction of Theorem 1.2, p. 52). -/
theorem perfect_berge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) : IsBerge G := by sorry

end StrongPerfectGraph.Main
