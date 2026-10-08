-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_complement_perfect
-- name    : StrongPerfectGraph.Main.complement_perfect
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:22:51.227717+00:00
-- url     : https://prove2.me/theorems/dee7edff-7bff-4f7b-ba91-89c7c30edd95
-- title:
--   1.1 — complement of a perfect graph
-- statement:
--   Let $G$ be a finite simple graph. If $G$ is perfect, then its complement is perfect:
--
--   $$G\text{ perfect}\quad\Longrightarrow\quad\overline G\text{ perfect}.$$
--
--   Perfection means equality of chromatic and clique numbers for every induced subgraph. This is Lovász’s theorem, stated as 1.1 and used in the reduction from 1.3 to the strong perfect graph theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 52, 1.1, cited from Lovász [16]

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- Lovász's theorem, cited as Theorem 1.1. -/
theorem complement_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) : IsPerfect Gᶜ := by sorry

end StrongPerfectGraph.Main
