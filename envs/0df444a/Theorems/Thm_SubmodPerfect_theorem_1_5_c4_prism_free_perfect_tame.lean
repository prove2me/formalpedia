-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_1_5_c4_prism_free_perfect_tame
-- name    : SubmodPerfect.theorem_1_5_c4_prism_free_perfect_tame
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:33.588401+00:00
-- url     : https://prove2.me/theorems/0f113b2d-1f7b-4ef4-ba6d-f38a95557de5
-- title:
--   Theorem 1.5 — (C4, prism)-free perfect graphs of maximum degree $\delta$ are $(1+\delta+\dots+\delta^{\delta+3},c,1+\delta+\dots+\delta^{\delta+3},3)$-tame
-- statement:
--   Let $c\in[\tfrac12,1)$, $\delta\ge1$ and
--
--   $$K=1+\delta+\delta^2+\dots+\delta^{\delta+3}.$$
--
--   The class of finite perfect graphs with no hole of length four, no induced prism, and every vertex of degree at most $\delta$ is $(K,c,K,3)$-tame:
--
--   1. for every such graph $G$ and every uniform weight function $w$ (weight $1/|X|$ on a nonempty set $X$, $0$ elsewhere) there are $K$ pairwise disjoint sets $L_1,\dots,L_K$, each $L_i$ an even set of $G\setminus\bigcup_{j<i}L_j$, such that every connected component $D$ of $G\setminus\bigcup_iL_i$ has at most $K$ neighbours and weight $w(D)\le c$; and
--   2. one program of the unit-cost RAM and one constant $C$, chosen after $c$ and $\delta$, compute such a tuple from $n$, the adjacency matrix of $G$, the weights and $c$ within $C\,(n+1)^3$ steps, for every such $G$ on $n$ vertices and every uniform $w$.
--
--   This is the paper's structure theorem: bounded-degree (C4, prism)-free perfect graphs have balanced separators made of a bounded number of iterated even sets, and these can be found in cubic time. Combined with Theorem 1.2 it gives a combinatorial polynomial-time algorithm for maximum weight independent set in this class (Theorem 1.6).
--
--   **Formalization Note** Graphs are on $\{0,\dots,n-1\}$ for every $n$; the machine, input layout (with $c$ as an input real) and output decoder are those of `SubmodPerfect.Tame`.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - reading: G is (k, c, d, m)-tame (one graph, O(|V(G)|^m) time) → the class of all graphs meeting the hypotheses is tame: one program and one constant C serve every graph of the class; reason: an O(·) bound for a single graph is meaningless; the uniform bound over the class is the non-vacuous reading
--   - encoding: uniform weight function w (w = 1/|X| on X, 0 elsewhere) → uniformWeight X with X nonempty; reason: 1/|X| is undefined for X = ∅; the paper's uniform weights have w(G) = 1
--   - encoding: constructed in O(|V(G)|^m) time → one program of the published unit-cost RAM (WilliamsonShmoys) and one constant C such that on input (n, adjacency matrix, w, c) the run halts within C·(n+1)^m steps with the separator in the output cells; graphs on Fin n; reason: the RAM has no real constants besides 0, so the threshold c is an input real cell; (n+1)^m avoids the degenerate n = 0
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 1.5, p.4

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Tame

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 1.5, p.4.

Let `c ∈ [1/2, 1)` and `δ` a positive integer. Every (C4, prism)-free perfect graph with maximum
degree `δ` is `(1 + δ + … + δ^{δ+3}, c, 1 + δ + … + δ^{δ+3}, 3)`-tame.

**Formalization Note.** Tameness is stated for the class of C4-free, prism-free, perfect graphs
on `Fin n` (all `n`) with maximum degree at most `δ`: (a) every such graph has a
`(w, K, c, K)`-even set separator for every uniform weight function `w`, `K = tameBound δ`; and
(b) one RAM program and one constant `C`, chosen after `c` and `δ`, construct such a separator
from `(n, G, w, c)` within `C · (n + 1)³` steps (`IsTameClass`, with the machine, input layout
and output decoder of `Definitions.Def_SubmodPerfect_Tame`). C4-free and prism-free are induced
(no hole of length four, no induced prism). -/
theorem theorem_1_5_c4_prism_free_perfect_tame (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (δ : ℕ)
    (hδ : 1 ≤ δ) :
    IsTameClass
      (fun _ G => IsC4Free G ∧ IsPrismFree G ∧ StrongPerfectGraph.Main.IsPerfect G ∧
        MaxDegreeLe G δ)
      (tameBound δ) c (tameBound δ) 3 := by sorry

end SubmodPerfect
