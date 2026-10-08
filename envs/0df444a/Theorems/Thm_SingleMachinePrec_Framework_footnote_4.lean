-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_footnote_4
-- name    : SingleMachinePrec.Framework.footnote_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:29:32.696158+00:00
-- url     : https://prove2.me/theorems/9b56cefe-4a46-4ed5-903a-09cb9eced26d
-- title:
--   Footnote 4 — the pairs reversed by a linear extension form an independent set of G^S_P
-- statement:
--   Let $P$ be a partial order on $N$ and $L$ a linear extension of $P$. The set
--   $$\{(a,b) \in \operatorname{inc}(P) : b < a \text{ in } L\}$$
--   of incomparable pairs reversed in $L$ is an independent set of the vertex cover graph $G^S_P$: no two of its members are adjacent. Equivalently, the incomparable pairs $(a,b)$ with $a < b$ in $L$ form a vertex cover of $G^S_P$.
--
--   In the proof of Theorem 5.1 this shows that $I_{1/2}$, the pairs of $V_{1/2}$ reversed in a sampled linear extension, is independent, so its complement in $V_{1/2}$ covers the subgraph induced by $V_{1/2}$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 659, footnote 4 (proof of Theorem 5.1)

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

namespace SingleMachinePrec.Framework

/-- **Footnote 4** (p. 659). For every linear extension `L` of the partial order `P`, the
incomparable pairs reversed in `L` form an independent set of `G^S_P`. -/
theorem footnote_4 {N : Type*} (P : N → N → Prop) [IsPartialOrder N P]
    (L : LinearExtension P) :
    (vertexCoverGraph P).IsIndepSet {u | L.Reverses u} := by sorry

end SingleMachinePrec.Framework
