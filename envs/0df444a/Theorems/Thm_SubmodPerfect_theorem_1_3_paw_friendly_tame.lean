-- Prove2me | Theorems.Thm_SubmodPerfect_theorem_1_3_paw_friendly_tame
-- name    : SubmodPerfect.theorem_1_3_paw_friendly_tame
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:26.87586+00:00
-- url     : https://prove2.me/theorems/f4bd847e-9e71-44f9-854c-bf9b5dd02a43
-- title:
--   Theorem 1.3 — paw-friendly graphs of maximum degree $\delta$ are $(1+\delta+\dots+\delta^{\delta+3},c,1+\delta+\dots+\delta^{\delta+3},3)$-tame
-- statement:
--   Let $c\in[\tfrac12,1)$, $\delta\ge1$ and $K=1+\delta+\dots+\delta^{\delta+3}$. The class of finite paw-friendly graphs in which every vertex has degree at most $\delta$ is $(K,c,K,3)$-tame:
--
--   1. every such $G$ and every uniform weight function $w$ admit a $(w,K,c,K)$-even set separator; and
--   2. one RAM program and one constant $C$ construct such a separator from $(n,G,w,c)$ within $C\,(n+1)^3$ steps, for every such $G$ on $n$ vertices and every uniform $w$.
--
--   $G$ is not assumed connected. Through Theorem 1.2 this yields a combinatorial polynomial-time algorithm for maximum weight independent set in bounded-degree paw-friendly graphs (Theorem 1.4).
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - reading: G is (k, c, d, m)-tame (one graph, O(|V(G)|^m) time) → the class of all graphs meeting the hypotheses is tame: one program and one constant C serve every graph of the class; reason: an O(·) bound for a single graph is meaningless; the uniform bound over the class is the non-vacuous reading
--   - encoding: uniform weight function w (w = 1/|X| on X, 0 elsewhere) → uniformWeight X with X nonempty; reason: 1/|X| is undefined for X = ∅; the paper's uniform weights have w(G) = 1
--   - encoding: constructed in O(|V(G)|^m) time → one program of the published unit-cost RAM (WilliamsonShmoys) and one constant C such that on input (n, adjacency matrix, w, c) the run halts within C·(n+1)^m steps with the separator in the output cells; graphs on Fin n; reason: the RAM has no real constants besides 0, so the threshold c is an input real cell; (n+1)^m avoids the degenerate n = 0
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Theorem 1.3, p.3 (restated and proved p.26–27)

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_Tame

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Theorem 1.3, p.3 (restated p.26).

Let `c ∈ [1/2, 1)` and `δ` a positive integer. Every paw-friendly graph with maximum degree `δ`
is `(1 + δ + … + δ^{δ+3}, c, 1 + δ + … + δ^{δ+3}, 3)`-tame.

**Formalization Note.** Tameness is stated for the class of paw-friendly graphs on `Fin n`
(all `n`) with maximum degree at most `δ`, with one RAM program and one constant for the whole
class (`IsTameClass`). `tameBound δ = ∑_{i=0}^{δ+3} δ^i`. -/
theorem theorem_1_3_paw_friendly_tame (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (δ : ℕ) (hδ : 1 ≤ δ) :
    IsTameClass (fun _ G => IsPawFriendly G ∧ MaxDegreeLe G δ) (tameBound δ) c (tameBound δ) 3 := by sorry

end SubmodPerfect
