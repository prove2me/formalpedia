-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_10
-- name    : RendezvousKn.Sym.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:16.120981+00:00
-- url     : https://prove2.me/theorems/aaf50d53-e008-4230-8e02-5fe4ce86c033
-- title:
--   Lemma 10, p. 11 — same-kind tactics with |F| ≥ (11/12)n have Var X ≥ 1/32
-- statement:
--   Fix $n\ge2$ and tactics $\tau_A,\tau_B$ that are of the same kind: both passive or both active (Definition 3). Let $F$ be their pair set and $X$ the match count for a uniformly random binding. If $|F|\ge\tfrac{11}{12}n$, then
--   $$\operatorname{Var}X\ \ge\ \frac1{32}.$$
--
--   This combines Lemma 9 (applied to $F$ as a bipartite graph) with Lemma 8, and is where the restriction to tactics of the same kind enters.
--
--   **Formalization Note** The proof's estimate $(n+1)/2\le\frac23n$ fails at $n=2$, but the statement is true there (the degree bound in the active case is $\lceil n/2\rceil\le\frac23 n$); it is posed as printed.
--
--   Differences from the source:
--   - encoding: τ_A, τ_B ∈ Θ^A or τ_A, τ_B ∈ Θ^P → IsPassive τ_A ↔ IsPassive τ_B; reason: every tactic is either passive or active, so 'both in one class' is 'same passivity'
--   - encoding: Var X → E X² − (E X)² (varX); reason: the two standard expressions of the variance are equal
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 11 (PDF 12), §3.5, Lemma 10

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_10 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n)
    (hkind : IsPassive τA ↔ IsPassive τB)
    (hF : (11 / 12 : ℝ) * n ≤ ((pairSet τA τB).card : ℝ)) :
    1 / 32 ≤ varX (pairSet τA τB) := by sorry

end RendezvousKn.Sym
