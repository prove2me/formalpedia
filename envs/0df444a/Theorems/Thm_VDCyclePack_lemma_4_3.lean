-- Prove2me | Theorems.Thm_VDCyclePack_lemma_4_3
-- name    : VDCyclePack.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:53.894613+00:00
-- url     : https://prove2.me/theorems/9fe5aec0-053c-4d72-92de-997d9cfa4cf3
-- title:
--   Lemma 4.3 (Structure), existence part: $q$ disjoint cycles, or a marked packing with properties 1–2 (time bound: lemma_4_3_polytime)
-- statement:
--   Let $q\ge2$, $a\ge2$, $L\ge3$ and $c\ge1$ be integers, and put $M=8q\lceil\log_2(q+2)\rceil$. Let $G$ be a finite graph with $n$ vertices. Then $G$ has $q$ vertex-disjoint cycles, or there is a marked packing $H$ (the union of a cycle packing) with the following properties.
--
--   1. In every fractional packing $x$ of $G$, of value $T$, the cycles not in $\mathcal C(H,L,c)$ have total weight at most
--   $$
--   \frac{n}{L+1}+\frac{4M+T}{c+1}.
--   $$
--   2. For every $R\subseteq\mathcal C(H,L,c)$ with $t=|R|$,
--   $$
--   \beta\Bigl(\bigcup_{C\in R}C\Bigr)\le 3ct+\frac{32t}{a}\bigl(\log_2(t+2)+5\bigr).
--   $$
--
--   Property 1 lets the candidate family keep half of the LP weight, and property 2 is the structural hypothesis of Theorem 4.2. This item is the existence part of Lemma 4.3; the polynomial-time part is the companion item `VDCyclePack.lemma_4_3_polytime`.
--
--   **Formalization Note** $c_H(C)$ counts the components of $C\cap H$ on vertices and edges; $\beta$ is the minimum feedback edge set; logarithms are base two.
--
--   Differences from the source:
--   - encoding: a marked packing H, A = V(H), A-paths in G − E(H) → H = P.sup id for a cycle packing P (a Finset of pairwise vertex-disjoint cycle subgraphs); A = H.verts; A-paths are IsAPath in G.deleteEdges H.edgeSet; reason: the paper's definitions (pp.10–11); same instances
--   - encoding: c_H(C), C(H, L, c), n = |V(G)| → contacts (components of the subgraph meet C ⊓ H), candidates G H L c, Fintype.card V; reason: the paper's definitions (pp.10, 13); same instances
--   - encoding: in every fractional packing of value T, the total weight of the cycles not in C(H, L, c) → ∀ x with IsFracPacking G x, the sum of x C over cycles G \ candidates, with T = value G x; reason: same statement; x is read only on cycles
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
--   - encoding: find q vertex-disjoint cycles in G → ∃ P, IsCyclePacking P ∧ P.card = q; reason: same statement
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.3, p.13

import Mathlib
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_IsFracPacking
import Definitions.Def_VDCyclePack_value
import Definitions.Def_VDCyclePack_candidates
import Definitions.Def_VDCyclePack_cycleRank
import Definitions.Def_VDCyclePack_bigM

namespace VDCyclePack

open Classical in
/-- **Lemma 4.3 (structure), existence.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.3, p.13: "Let q ≥ 2, a ≥ 2, L ≥ 3, and c ≥ 1 be integers, and put
M = 8q⌈log(q+2)⌉. In polynomial time, one can either find q vertex-disjoint cycles in G, or find a
marked packing H with the following properties. 1. In every fractional packing of value T, the
cycles not in C(H, L, c) have total weight at most n/(L + 1) + (4M + T)/(c + 1). 2. For every
R ⊆ C(H, L, c) with t = |R|, β(⋃_{C∈R} C) ≤ 3ct + (32t/a)(log(t + 2) + 5)."

For integers `q ≥ 2`, `a ≥ 2`, `L ≥ 3`, `c ≥ 1` and `M = 8q⌈log₂(q + 2)⌉`, either `G` has a cycle
packing of size `q`, or some cycle packing `P` with union `H = ⋃ P` satisfies: (1) for every
fractional packing `x` of `G`, of value `T`, the cycles of `G` outside `𝒞(H, L, c)` carry total weight
at most `n/(L+1) + (4M + T)/(c+1)`, `n = |V(G)|`; (2) for every `R ⊆ 𝒞(H, L, c)`, `t = |R|`,
`β(⋃_{C∈R} C) ≤ 3ct + (32t/a)(log₂(t + 2) + 5)`.

**Formalization Note.** This item is the existence of the dichotomy; the polynomial-time clause
is `lemma_4_3_polytime`. A marked packing is the union `P.sup id` of a cycle packing `P`. Item 1
holds for every fractional packing of `G`, of any value. -/
theorem lemma_4_3 {V : Type*} [Fintype V] (G : SimpleGraph V) (q a L c : ℕ) (hq : 2 ≤ q)
    (ha : 2 ≤ a) (hL : 3 ≤ L) (hc : 1 ≤ c) :
    (∃ P : Finset G.Subgraph, IsCyclePacking P ∧ P.card = q) ∨
    ∃ P : Finset G.Subgraph, IsCyclePacking P ∧
      (∀ x : G.Subgraph → ℝ, IsFracPacking G x →
        ∑ C ∈ cycles G \ candidates G (P.sup id) L c, x C ≤
          (Fintype.card V : ℝ) / (L + 1) + (4 * bigM q + value G x) / (c + 1)) ∧
      ∀ R ⊆ candidates G (P.sup id) L c,
        (cycleRank (R.sup id) : ℝ) ≤
          3 * c * R.card + 32 * R.card / a * (Real.logb 2 (R.card + 2) + 5) := by sorry

end VDCyclePack
