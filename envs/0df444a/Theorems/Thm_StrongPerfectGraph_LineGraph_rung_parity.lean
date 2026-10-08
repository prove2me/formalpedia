-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_rung_parity
-- name    : StrongPerfectGraph.LineGraph.rung_parity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:48:07.350829+00:00
-- url     : https://prove2.me/theorems/79d856eb-d11b-4d5e-bcf6-eb49cac00f93
-- title:
--   8.1, p. 99 — all uv-rungs of a strip system have the same parity
-- statement:
--   Let $(S, N)$ be a $J$-strip system in a Berge graph $G$, where $J$ is $3$-connected. Then for every edge $uv$ of $J$, all $uv$-rungs have lengths of the same parity:
--
--   $$|R| \equiv |R'| \pmod 2 \quad \text{for all $uv$-rungs } R, R'.$$
--
--   Hence any choice of one rung per edge of $J$ induces the line graph of a bipartite subdivision of $J$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 99, 8.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
import Definitions.Def_StrongPerfectGraph_LineGraph_IsStripSystem

namespace StrongPerfectGraph.LineGraph

theorem rung_parity {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (S : W → W → Set V) (N : W → Set V) (hSN : IsStripSystem J G S N) :
    ∀ u v : W, J.Adj u v → ∀ R R' : List V, IsRung G S N u v R → IsRung G S N u v R' →
      (R.length - 1) % 2 = (R'.length - 1) % 2 := by sorry

end StrongPerfectGraph.LineGraph
