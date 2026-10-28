-- Prove2me | Theorems.Thm_RuralPostman_NPC_uhc_polyReducible_urp
-- name    : RuralPostman.NPC.uhc_polyReducible_urp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:36.430723+00:00
-- url     : https://prove2.me/theorems/79cd641f-f659-4740-aedd-1ffd628adf24
-- title:
--   §2, p. 5, proof of the Theorem — UNDIRECTED HAMILTON CIRCUIT ∝ UNDIRECTED RURAL POSTMAN
-- statement:
--   UNDIRECTED HAMILTON CIRCUIT is polynomially reducible to UNDIRECTED RURAL POSTMAN:
--   $$
--   \text{UNDIRECTED HAMILTON CIRCUIT} \;\propto\; \text{UNDIRECTED RURAL POSTMAN}.
--   $$
--   That is, there is a function $f$ from words to words over the alphabet $\{0,1,-,\#\}$, computable by a one-tape Turing machine in polynomial time, such that a word $x$ is the code of an undirected graph on at least three vertices with a hamilton circuit if and only if $f(x)$ is the code of a rural postman instance with an undirected postman's tour of weight at most its threshold.
--
--   This is the first of the two reductions displayed in the proof; together with the NP-completeness of UNDIRECTED HAMILTON CIRCUIT it gives the NP-hardness half of the undirected case of the Theorem.
--
--   **Formalization Note** The languages consist of codes: `uhcLang` holds the codes `dhpCode adj` of symmetric Boolean matrices on $n\ge3$ nodes with a hamilton circuit, `urpLang` the codes `rpCode I` of yes-instances. `PolyReducible` quantifies over all words, so the reducing function must also send words that code no symmetric matrix on at least three nodes to codes outside `urpLang` (or to words that are no code).
--
--   Differences from the source:
--   - reading: "L ∝ M means that any instance of L can be reduced to an instance of M in a polynomial number of steps" → CookPvsNP.PolyReducible L M: a polynomial-time computable f : List BSym → List BSym with x ∈ L ↔ f x ∈ M for every word x; reason: Karp's polynomial transformation; the languages are sets of instance codes, so f must also handle words that code no instance
--   - reading: UNDIRECTED HAMILTON CIRCUIT on H = (V,E) → uhcLang: the codes dhpCode adj of symmetric Bool matrices on n ≥ 3 nodes with HasHamiltonCircuit adj; reason: an undirected cycle needs at least 3 nodes (paper.md reading 4)
--   - reading: G = (N,A) a graph with w: A → ℕ∪{0}, threshold k → RPInstance: nodes Fin n, a list of arcs (tail, head, weight ∈ ℕ, required?) with parallel arcs and loops allowed, k ∈ ℕ; reason: the paper does not restrict G to simple graphs; the instances produced by the reductions are simple, and the weights and k of the paper are natural numbers
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: instances of the decision problems → languages over the four-letter alphabet BSym: rpCode (n, number of arcs, tail, head, weight, required-bit of each arc, k in binary) and dhpCode (n and the adjacency matrix in binary); reason: standard binary encodings; each code determines its instance
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 5, §2, proof of the Theorem, "We shall show that UNDIRECTED HAMILTON CIRCUIT ∝ UNDIRECTED RURAL POSTMAN, …"

import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

theorem uhc_polyReducible_urp : CookPvsNP.PolyReducible uhcLang urpLang := by sorry

end RuralPostman.NPC
