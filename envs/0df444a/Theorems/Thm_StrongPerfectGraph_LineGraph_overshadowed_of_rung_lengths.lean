-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_overshadowed_of_rung_lengths
-- name    : StrongPerfectGraph.LineGraph.overshadowed_of_rung_lengths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:07.829573+00:00
-- url     : https://prove2.me/theorems/8ba14680-ead5-4613-aa29-bf6ad840f6a9
-- title:
--   8.2, p. 99 — rungs of length 0 and of positive length give an overshadowed appearance
-- statement:
--   Let $(S, N)$ be a $J$-strip system in a Berge graph $G$, where $J$ is $3$-connected. If there is an edge $uv$ of $J$ such that some $uv$-rung has length $0$ and another $uv$-rung has length at least $1$, then there is an overshadowed appearance of $J$ in $G$.
--
--   Together with 7.5 this shows that, in the absence of enlargements and balanced skew partitions, the nondegeneracy of a strip system does not depend on the choice of rungs.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 99, 8.2

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
import Definitions.Def_StrongPerfectGraph_LineGraph_IsStripSystem
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed

namespace StrongPerfectGraph.LineGraph

theorem overshadowed_of_rung_lengths {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (S : W → W → Set V) (N : W → Set V) (hSN : IsStripSystem J G S N)
    (u v : W) (huv : J.Adj u v) (R R' : List V)
    (hR : IsRung G S N u v R) (hR' : IsRung G S N u v R')
    (h₀ : R.length - 1 = 0) (h₁ : 1 ≤ R'.length - 1) :
    HasOvershadowedAppearance J G := by sorry

end StrongPerfectGraph.LineGraph
