-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_lemma_9
-- name    : TwoOptAllExp.TSP.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:13:46.234697+00:00
-- url     : https://prove2.me/theorems/4c182115-affc-4fa0-a484-8b4b898916ab
-- title:
--   Lemma 9 — tours of $G_n$ are the 2-regular subgraphs with the layer-path invariant
-- statement:
--   Let $n\ge1$. An edge set $H$ forms a tour of $G_n$ if and only if it is a 2-regular subgraph of $G_n$ satisfying the layer-path invariant.
--
--   This characterization reduces the global Hamiltonicity of an edge set to a condition on each layer.
--
--   Differences from the source:
--   - reading: restriction of $H$ to $F_i$ → the edges of $H$ with both endpoints in $F_i$, where $F_i$ contains all its interfaces, shared with the adjacent layers; reason: p. 14: paths of consecutive layers overlap on their identified interfaces; a spanning path of $F_n$ must contain the $X_n$- and $Y_n$-interfaces
--   - encoding: a 2-regular subgraph → every vertex of $G_n$ lies on exactly two edges of $H$; reason: the invariant spans all vertices, so a subgraph on fewer vertices is excluded in either reading
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 9, p. 15

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_LayerPath

namespace TwoOptAllExp.TSP

/-- **Lemma 9**, p. 15: an edge set forms a tour of `G_n` if and only if it is a 2-regular subgraph
of `G_n` satisfying the layer-path invariant. -/
theorem lemma_9 (n : ℕ) (hn : 1 ≤ n) (H : Finset (Sym2 (Vtx n))) :
    IsTourOf (G n) H ↔ IsTwoRegularSubgraph H ∧ LayerPathInvariant H := by sorry

end TwoOptAllExp.TSP
