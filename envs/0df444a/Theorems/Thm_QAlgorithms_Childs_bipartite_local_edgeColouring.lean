-- Prove2me | Theorems.Thm_QAlgorithms_Childs_bipartite_local_edgeColouring
-- name    : QAlgorithms.Childs.bipartite_local_edgeColouring
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:36:04.925507+00:00
-- url     : https://prove2.me/theorems/d94aafa9-3aca-4297-bba9-3e73c0f61209
-- title:
--   Local d²-edge-colouring of a bipartite graph of maximum degree d
-- statement:
--   Fix integers $N,d\ge 0$. There is a single colouring rule $c$, chosen before the graph, that assigns to an ordered pair of vertices $\alpha,\beta\in\{1,\dots,N\}$ a colour $c\big((\alpha,s(\alpha),L_\alpha),(\beta,s(\beta),L_\beta)\big)\in\mathbb N\times\mathbb N$ that depends only on the two vertices, their sides $s(\alpha),s(\beta)$ of the bipartition, and their neighbour lists $L_\alpha,L_\beta$, with the following property.
--
--   Let $G$ be an undirected simple graph on the vertex set $\{1,\dots,N\}$ with a bipartition $s:V\to\{\mathrm{left},\mathrm{right}\}$ (every edge joins the two sides) and maximum degree at most $d$, and let $L_v$ be any duplicate-free list of the neighbours of each vertex $v$. Then the map $\{\alpha,\beta\}\mapsto c\big((\alpha,s(\alpha),L_\alpha),(\beta,s(\beta),L_\beta)\big)$ is a proper edge colouring of $G$:
--
--   1. it is symmetric on edges, so each edge receives one colour;
--   2. two distinct edges sharing a vertex receive distinct colours;
--   3. the number of distinct colours used on the edges of $G$ satisfies
--
--   $$
--   \#\{\,c(\alpha,\beta) : \alpha\beta\in E(G)\,\}\le d^2 .
--   $$
--
--   In the source the colour of an edge $\alpha\beta$ with $\alpha$ on the left is $(\mathrm{idx}(\alpha,\beta),\mathrm{idx}(\beta,\alpha))$, where $\mathrm{idx}(\alpha,\beta)$ is the position of $\beta$ in the neighbour list of $\alpha$. The lemma is the colouring step of the simulation of sparse Hamiltonians: the edges of each colour class form a matching, whose Hamiltonian is simulated separately before the pieces are combined by a product formula.
--
--   **Formalization Note** The source's "efficiently computable" has no machine model, so the running time of the rule is not formalized; what is kept is that one rule serves every graph and reads only the two endpoints' local data (two neighbour-list queries per edge). Colours are pairs of natural numbers rather than elements of $[d]\times[d]$ so that the rule is total at $d=0$; the bound $d^2$ is on the colours actually used on edges.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 143, Lemma 27.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Walk
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Lemma 27.1 (PDF p. 143). "Suppose we are given an undirected, bipartite graph `G`
with `N` vertices and maximum degree `d`, and that we can efficiently compute the neighbors of
any given vertex. Then there is an efficiently computable edge coloring of `G` with at most `d²`
colors."

Formal reading: for every `N` and `d` there is one colouring rule `rule`, fixed before the graph,
whose value on an edge `{α, β}` depends only on the two endpoints, their sides of the
bipartition and their neighbour lists (two neighbour-list queries). For every bipartite graph `G`
on `Fin N` with a given bipartition `side` and maximum degree at most `d`, and every enumeration
`nbr` of the neighbours of each vertex, the map `{α, β} ↦ rule (α, side α, nbr α) (β, side β,
nbr β)` is a proper edge colouring of `G` (symmetric on edges, distinct colours on distinct edges
at a common vertex) that uses at most `d²` distinct colours on the edges of `G`.

Not formalized: the running time of `rule` ("efficiently computable"); the source gives no
machine model. Graph-independence and locality of `rule` are the formal content kept. Colours
live in `ℕ × ℕ` rather than `Fin d × Fin d` so that the rule is total at `d = 0`; the bound
`≤ d²` is on the set of colours actually used on edges. -/
theorem bipartite_local_edgeColouring (N d : ℕ) :
    ∃ rule : Fin N × Bool × List (Fin N) → Fin N × Bool × List (Fin N) → ℕ × ℕ,
      ∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (side : Fin N → Bool),
        IsBipartition G side → G.maxDegree ≤ d →
        ∀ nbr : Fin N → List (Fin N), IsNeighbourList G nbr →
          IsProperEdgeColouring G (fun u v => rule (u, side u, nbr u) (v, side v, nbr v)) ∧
          ((Finset.univ.filter fun p : Fin N × Fin N => G.Adj p.1 p.2).image
              fun p => rule (p.1, side p.1, nbr p.1) (p.2, side p.2, nbr p.2)).card ≤ d ^ 2 := by
  sorry

end QAlgorithms.Childs
