-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_5_7_paw_friendly
-- name    : SubmodPerfect.theorem_5_7_paw_friendly
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:17.949987+00:00
-- url     : https://prove2.me/theorems/7c5e1151-eb51-4367-a98e-2454090c25c8
-- title:
--   Theorem 5.7 — (C4, prism)-free perfect graphs are paw-friendly
-- statement:
--   Every finite (C4, prism)-free perfect graph $G$ is paw-friendly: $G$ is perfect, and in every induced subgraph $H$ of $G$, for every paw of $H$ with edge set $\{ab_1,ab_2,b_1b_2,ac\}$, with respect to $H$ either $a$ breaks $\{c,b_1,b_2\}$, or $b_1$ breaks $\{c,b_2\}$, or $b_2$ breaks $\{c,b_1\}$.
--
--   This transfers every result about paw-friendly graphs, in particular Theorem 1.3, to (C4, prism)-free perfect graphs.
--
--   Differences from the source: none.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 5.7, p.19

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 5.7, p.19.

Every (C4, prism)-free perfect graph is paw-friendly. -/
theorem theorem_5_7_paw_friendly {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hC4 : IsC4Free G) (hprism : IsPrismFree G) :
    IsPawFriendly G := by sorry

end SubmodPerfect
