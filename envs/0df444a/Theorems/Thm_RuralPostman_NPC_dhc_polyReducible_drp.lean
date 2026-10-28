-- Prove2me | Theorems.Thm_RuralPostman_NPC_dhc_polyReducible_drp
-- name    : RuralPostman.NPC.dhc_polyReducible_drp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:30.67266+00:00
-- url     : https://prove2.me/theorems/e0024f7d-4b1d-469b-89cb-4a3cde5adf2f
-- title:
--   §2, p. 5, proof of the Theorem — DIRECTED HAMILTON CIRCUIT ∝ DIRECTED RURAL POSTMAN
-- statement:
--   DIRECTED HAMILTON CIRCUIT is polynomially reducible to DIRECTED RURAL POSTMAN:
--   $$
--   \text{DIRECTED HAMILTON CIRCUIT} \;\propto\; \text{DIRECTED RURAL POSTMAN}.
--   $$
--   That is, there is a function $f$ from words to words over the alphabet $\{0,1,-,\#\}$, computable by a one-tape Turing machine in polynomial time, such that a word $x$ is the code of a directed graph with a hamilton circuit if and only if $f(x)$ is the code of a rural postman instance with a directed postman's tour of weight at most its threshold.
--
--   This is the second of the two reductions displayed in the proof; together with the NP-completeness of DIRECTED HAMILTON CIRCUIT it gives the NP-hardness half of the directed case of the Theorem.
--
--   **Formalization Note** `dhcLang` holds the codes `dhpCode adj` of the Boolean adjacency matrices with `HasHamiltonCircuit adj` (on one vertex this requires a loop; on zero vertices it holds vacuously), `drpLang` the codes `rpCode I` of yes-instances of the directed problem. `PolyReducible` quantifies over all words, so the reducing function must also handle words that code no graph.
--
--   Differences from the source:
--   - reading: "L ∝ M means that any instance of L can be reduced to an instance of M in a polynomial number of steps" → CookPvsNP.PolyReducible L M: a polynomial-time computable f : List BSym → List BSym with x ∈ L ↔ f x ∈ M for every word x; reason: Karp's polynomial transformation; the languages are sets of instance codes, so f must also handle words that code no instance
--   - encoding: DIRECTED HAMILTON CIRCUIT on H = (V,E) → dhcLang: the codes dhpCode adj of Bool matrices with HasHamiltonCircuit adj (a one-vertex graph is a yes-instance iff it has a loop; the empty graph is a yes-instance); reason: the paper is silent on graphs with fewer than 2 nodes; these conventions are those of the published SchedComplexity.NoWait.DirectedGraphs
--   - reading: G = (N,A) a graph with w: A → ℕ∪{0}, threshold k → RPInstance: nodes Fin n, a list of arcs (tail, head, weight ∈ ℕ, required?) with parallel arcs and loops allowed, k ∈ ℕ; reason: the paper does not restrict G to simple graphs; the instances produced by the reductions are simple, and the weights and k of the paper are natural numbers
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: instances of the decision problems → languages over the four-letter alphabet BSym: rpCode (n, number of arcs, tail, head, weight, required-bit of each arc, k in binary) and dhpCode (n and the adjacency matrix in binary); reason: standard binary encodings; each code determines its instance
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 5, §2, proof of the Theorem, "… DIRECTED HAMILTON CIRCUIT ∝ DIRECTED RURAL POSTMAN, …"

import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

theorem dhc_polyReducible_drp : CookPvsNP.PolyReducible dhcLang drpLang := by sorry

end RuralPostman.NPC
