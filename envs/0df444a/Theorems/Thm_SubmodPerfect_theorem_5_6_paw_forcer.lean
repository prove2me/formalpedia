-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_5_6_paw_forcer
-- name    : SubmodPerfect.theorem_5_6_paw_forcer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:03.994996+00:00
-- url     : https://prove2.me/theorems/e1f6a850-44c3-4adb-b0f8-1a98bc81def2
-- title:
--   Theorem 5.6 — paws are forcers for (C4, prism)-free perfect graphs
-- statement:
--   Let $G$ be a (C4, prism)-free perfect graph and let $\{a,c,b_1,b_2\}$ induce a paw with edge set $\{ab_1,ab_2,b_1b_2,ac\}$. Then
--
--   $$a\text{ breaks }\{c,b_1,b_2\},\quad\text{or}\quad b_1\text{ breaks }\{c,b_2\},\quad\text{or}\quad b_2\text{ breaks }\{c,b_1\}.$$
--
--   So every paw has a center in the sense of forcers, which is the key input of the decomposition of Sections 6–7.
--
--   Differences from the source: none.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 5.6, p.19

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 5.6, p.19.

Let `G` be a (C4, prism)-free perfect graph and `P` a paw in `G` with vertex set `{a, c, b₁, b₂}`
and edge set `{ab₁, ab₂, b₁b₂, ac}`. Then either `a` breaks `{c, b₁, b₂}`, or `b₁` breaks
`{c, b₂}`, or `b₂` breaks `{c, b₁}`.

**Formalization Note.** The paw is induced (`c` is non-adjacent to `b₁`, `b₂`). Breaking is in
`G`. -/
theorem theorem_5_6_paw_forcer {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hperf : StrongPerfectGraph.Main.IsPerfect G) (hC4 : IsC4Free G) (hprism : IsPrismFree G)
    (a c b₁ b₂ : V) (hpaw : IsPaw G a c b₁ b₂) :
    BreaksIn G Finset.univ a {c, b₁, b₂} ∨ BreaksIn G Finset.univ b₁ {c, b₂} ∨
      BreaksIn G Finset.univ b₂ {c, b₁} := by sorry

end SubmodPerfect
