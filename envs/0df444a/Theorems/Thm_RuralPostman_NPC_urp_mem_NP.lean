-- Prove2me | Theorems.Thm_RuralPostman_NPC_urp_mem_NP
-- name    : RuralPostman.NPC.urp_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:43.911043+00:00
-- url     : https://prove2.me/theorems/18c2d9b2-6d4b-40a5-99e0-deb9abf85f8f
-- title:
--   §2, p. 5, proof of the Theorem — UNDIRECTED RURAL POSTMAN is solvable by polynomial-depth backtrack search (∈ NP)
-- statement:
--   UNDIRECTED RURAL POSTMAN belongs to NP:
--   $$
--   \text{UNDIRECTED RURAL POSTMAN} \in \mathrm{NP}.
--   $$
--   Here NP is defined via checking relations: a language $L$ over a finite alphabet is in NP if there are a polynomial-time decidable relation $R(w,y)$ and an exponent $k$ such that $w\in L$ iff some certificate $y$ with $|y|\le|w|^k$ satisfies $R(w,y)$.
--
--   This is the membership half of the undirected case of the Theorem, which the paper calls obvious. Postman's tours are not length-bounded (arcs of weight $0$ may be repeated arbitrarily often), so a certificate must be chosen with care.
--
--   **Formalization Note** The language is `urpLang`, the codes `rpCode I` of rural postman instances with an undirected postman's tour of weight $\le k$; NP is `CookPvsNP.NP` over the four-letter alphabet `BSym`.
--
--   Differences from the source:
--   - reading: "solvability of UNDIRECTED (DIRECTED) RURAL POSTMAN by polynomial-depth backtrack search, which is obvious" → membership in CookPvsNP.NP BSym (a polynomial-time checking relation with certificates of polynomial length); reason: a polynomial-depth backtrack search is a nondeterministic polynomial-time algorithm
--   - reading: G = (N,A) a graph with w: A → ℕ∪{0}, threshold k → RPInstance: nodes Fin n, a list of arcs (tail, head, weight ∈ ℕ, required?) with parallel arcs and loops allowed, k ∈ ℕ; reason: the paper does not restrict G to simple graphs; the instances produced by the reductions are simple, and the weights and k of the paper are natural numbers
--   - reading: a postman's tour is an "undirected (directed) cycle traversing each arc in R at least once" → a closed walk: a cyclic list of arc traversals in which nodes and arcs may repeat; the empty list is allowed; reason: the paper's own tour traverses each arc of R twice, so "cycle" means closed walk (paper.md reading 3); the empty tour matters only when R = ∅, where every reading gives weight 0
--   - encoding: instances of the decision problems → languages over the four-letter alphabet BSym: rpCode (n, number of arcs, tail, head, weight, required-bit of each arc, k in binary) and dhpCode (n and the adjacency matrix in binary); reason: standard binary encodings; each code determines its instance
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 5, §2, proof of the Theorem, "… the solvability of UNDIRECTED (DIRECTED) RURAL POSTMAN by polynomial-depth backtrack search, which is obvious."

import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

theorem urp_mem_NP : urpLang ∈ CookPvsNP.NP ProjSchedTW.Complexity.BSym := by sorry

end RuralPostman.NPC
