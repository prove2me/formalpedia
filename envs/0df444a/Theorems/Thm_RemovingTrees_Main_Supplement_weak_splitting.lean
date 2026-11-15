-- Prove2me | Theorems.Thm_RemovingTrees_Main_Supplement_weak_splitting
-- name    : RemovingTrees.Main.Supplement.weak_splitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:17:03.94621+00:00
-- url     : https://prove2.me/theorems/b27dde2f-35d3-4b00-9261-66bb65b5bc96
-- title:
--   Theorem 4.1 — Weak splitting into ⌊(1−ε)k⌋- and ⌊δk⌋-edge-connected spanning subgraphs
-- statement:
--   Let $G=(V,E)$ be a finite undirected multigraph on at least two vertices; loops and parallel edges are allowed. For an edge set $F\subseteq E$ and a vertex set $S\subseteq V$, write $\delta_F(S)$ for the set of edges of $F$ with exactly one endpoint in $S$. The spanning subgraph $(V,F)$ is $b$-edge-connected when $|\delta_F(S)|\ge b$ for every $\varnothing\ne S\subsetneq V$; the graph $G$ is $k$-edge-connected when $(V,E)$ is. Splitting $G$ means partitioning its edge set as $E=A\sqcup(E\setminus A)$, which gives two spanning subgraphs on the full vertex set.
--
--   **Theorem (weak splitting).** For every $\epsilon>0$ there is a $\delta>0$ such that for every positive integer $k$ and every $k$-edge-connected multigraph $G=(V,E)$ there is an edge set $A\subseteq E$ with
--
--   $$
--   |\delta_A(S)|\ \ge\ \lfloor(1-\epsilon)k\rfloor
--   \quad\text{and}\quad
--   |\delta_{E\setminus A}(S)|\ \ge\ \lfloor\delta k\rfloor
--   \qquad\text{for every }\varnothing\ne S\subsetneq V .
--   $$
--
--   Here $\delta$ depends on $\epsilon$ only, not on $k$ or $G$. In the notation of Bang-Jensen–Yeo and DeVos, where $f(k_1,k_2)$ is the least integer such that every $f(k_1,k_2)$-edge-connected graph splits into a $k_1$- and a $k_2$-edge-connected spanning subgraph, the theorem says $f(\lfloor(1-\epsilon)k\rfloor,\lfloor\delta k\rfloor)\le k$.
--
--   This is a weak form of the splitting hypothesis: one part keeps almost all of the connectivity while the other still has connectivity linear in $k$.
--
--   **Formalization Note** The statement reuses the published base model `RemovingTrees_Main_GraphModel`: vertices are `Fin n` with $n\ge2$, edges are individually labelled by `Fin m`, and `CutLower G F b` says every nonempty proper shore has at least $b$ edges of $F$ crossing it. The floors are integer floors cast to $\mathbb R$. For $\epsilon\ge1$ the first bound is at most $0$ and that clause holds trivially, as in the source. The proof on p.12 gives the explicit value $\delta=\epsilon/(176\cdot44^{10\eta_s^{-2}})$ after reducing to $\epsilon\le1/2$ and even $k$; the statement quantifies $\delta$ existentially, exactly as printed, and imposes neither reduction. The function $f$ is not defined in Lean; the direct splitting statement is the theorem's content.
--
--   Differences from the source:
--   - encoding: k-edge-connected multigraph on at least two vertices, split into two spanning subgraphs → `MultiGraph n m` with `2 ≤ n`, `CutLower G Finset.univ k`, and an edge set `A` with parts `A` and `Finset.univ \ A` measured by `CutLower`; reason: a labelled-edge multigraph with loops and parallel edges is exactly the source's graph class, and a partition of the edge set is determined by one part.
--   - encoding: the restatement f(⌊(1−ε)k⌋, ⌊δk⌋) ≤ k → omitted, the direct splitting statement only; reason: the source introduces it with "i.e." as an equivalent restatement of the splitting claim, so no instance changes.
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Theorem 4.1, p.12; definitions §1 p.1 and §2 p.3; canonical PDF SHA-256 427511aeca336c17cec98e861a117b1a4ba95e875c8834100b984769c39e6da4

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main.Supplement

open RemovingTrees.Main

/-- Theorem 4.1, p.12 (weak splitting). For every `ε > 0` there is `δ > 0`, chosen
before `k` and the graph, such that every `k`-edge-connected finite multigraph
(`n ≥ 2` vertices, labelled edges, loops and parallel edges allowed, `k ≥ 1`) has an
edge partition `A`, `E \ A` into two spanning subgraphs whose own edge connectivities
are at least `⌊(1 - ε) k⌋` and `⌊δ k⌋` respectively. -/
theorem weak_splitting :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n m k : ℕ) (G : MultiGraph n m),
        2 ≤ n → 0 < k → CutLower G Finset.univ k →
        ∃ A : Finset (Fin m),
          CutLower G A ((⌊(1 - ε) * (k : ℝ)⌋ : ℤ) : ℝ) ∧
          CutLower G (Finset.univ \ A) ((⌊δ * (k : ℝ)⌋ : ℤ) : ℝ) := by sorry

end RemovingTrees.Main.Supplement
