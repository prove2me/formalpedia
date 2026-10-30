-- Prove2me | Theorems.Thm_RuralPostman_NPC_theorem_rpp_np_complete
-- name    : RuralPostman.NPC.theorem_rpp_np_complete
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:52.848867+00:00
-- url     : https://prove2.me/theorems/5a23f548-b826-4f10-a7ad-29771d93d594
-- title:
--   §2 Theorem, p. 5 — the rural postman problem is NP-complete on undirected and on directed graphs
-- statement:
--   **Theorem** (Lenstra and Rinnooy Kan). The rural postman problem is polynomial complete both in the case that $G$ is undirected and in the case that $G$ is directed.
--
--   The **rural postman problem** asks, for a graph $G=(N,A)$ with weights $w:A\to\mathbb N\cup\{0\}$, a set $R\subseteq A$ of required arcs and a bound $k$, whether there is a closed walk traversing every arc of $R$ at least once with total weight at most $k$ (arcs traversed in either direction if $G$ is undirected, from tail to head if $G$ is directed). The statement is proved relative to the classical fact, established by Karp, that UNDIRECTED and DIRECTED HAMILTON CIRCUIT are NP-complete: assuming
--
--   1. UNDIRECTED HAMILTON CIRCUIT is NP-complete, and
--   2. DIRECTED HAMILTON CIRCUIT is NP-complete,
--
--   we have
--   $$
--   \text{UNDIRECTED RURAL POSTMAN is NP-complete} \quad\text{and}\quad \text{DIRECTED RURAL POSTMAN is NP-complete.}
--   $$
--
--   The Chinese postman problem ($R=A$) is solvable in polynomial time; the Theorem shows that requiring only a subset of the arcs makes the problem as hard as the travelling salesman problem, on undirected and on directed graphs alike.
--
--   **Formalization Note** NP-completeness is `CookPvsNP.NPComplete` (one-tape Turing machines; membership in NP and polynomial-time many-one reducibility from every NP language over any finite nonempty alphabet). The four problems are languages of binary instance codes over the alphabet `BSym`: `uhcLang`, `dhcLang`, `urpLang`, `drpLang` from `RuralPostman.NPC.Instances`. Tours are unrestricted closed walks (no length bound); the empty tour is allowed. Hamilton circuits are cyclic orderings of all nodes, on symmetric matrices with $n\ge 3$ in the undirected case.
--
--   Differences from the source:
--   - reading: "follows from the polynomial completeness of UNDIRECTED (DIRECTED) HAMILTON CIRCUIT, which is established in [6]" → hypotheses hU : CookPvsNP.NPComplete uhcLang and hD : CookPvsNP.NPComplete dhcLang; reason: the paper imports this fact from Karp [6]; it is not proved on the platform, so the goal is stated relative to it (paper.md reading 5)
--   - reading: "polynomial complete" (Karp [6]) → CookPvsNP.NPComplete: membership in NP plus polynomial-time many-one reducibility of every NP language, for one-tape Turing machines; reason: Karp's notion is NP-completeness under polynomial-time many-one reductions
--   - reading: UNDIRECTED HAMILTON CIRCUIT on H = (V,E) → uhcLang: the codes dhpCode adj of symmetric Bool matrices on n ≥ 3 nodes with HasHamiltonCircuit adj; reason: an undirected cycle needs at least 3 nodes (paper.md reading 4)
--   - encoding: DIRECTED HAMILTON CIRCUIT on H = (V,E) → dhcLang: the codes dhpCode adj of Bool matrices with HasHamiltonCircuit adj (one vertex: yes iff a loop; zero vertices: yes); reason: conventions of the published SchedComplexity.NoWait.DirectedGraphs on graphs with fewer than 2 nodes, where the paper is silent
--   - reading: G = (N,A) a graph with w: A → ℕ∪{0}, threshold k → RPInstance: nodes Fin n, a list of arcs (tail, head, weight ∈ ℕ, required?) with parallel arcs and loops allowed, k ∈ ℕ; reason: the paper does not restrict G to simple graphs; the instances produced by the reductions are simple, and the weights and k of the paper are natural numbers
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: instances of the decision problems → languages over the four-letter alphabet BSym: rpCode (n, number of arcs, tail, head, weight, required-bit of each arc, k in binary) and dhpCode (n and the adjacency matrix in binary); reason: standard binary encodings; each code determines its instance
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 5, §2, Theorem

import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

theorem theorem_rpp_np_complete (hU : CookPvsNP.NPComplete uhcLang)
    (hD : CookPvsNP.NPComplete dhcLang) :
    CookPvsNP.NPComplete urpLang ∧ CookPvsNP.NPComplete drpLang := by sorry

end RuralPostman.NPC
