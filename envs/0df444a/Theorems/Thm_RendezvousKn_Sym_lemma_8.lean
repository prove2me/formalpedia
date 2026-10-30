-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_8
-- name    : RendezvousKn.Sym.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:12.421786+00:00
-- url     : https://prove2.me/theorems/43262fb4-7e15-4856-b32e-559569efb202
-- title:
--   Lemma 8, p. 9 — at least α·C(n, 2) disjoint pairs in F imply Var X ≥ α
-- statement:
--   Fix $n\ge2$ and tactics $\tau_A,\tau_B$ with pair set $F$ and match count $X$ for a uniformly random binding. Two pairs $(i,j),(i',j')$ are disjoint if $i\neq i'$ and $j\neq j'$. Suppose that $F$ contains at least
--   $$\alpha\binom n2$$
--   disjoint pairs (unordered pairs $\{e,f\}$ of distinct elements of $F$ that are disjoint), for some constant $\alpha>0$. Then
--   $$\operatorname{Var}X\ \ge\ \alpha.$$
--
--   Many disjoint pairs mean many positively correlated indicator pairs, which is how the combinatorics of $F$ yields the variance needed by Lemma 6.
--
--   Differences from the source:
--   - reading: 'at least α(n choose 2) disjoint pairs in F' → the number of 2-element subsets {e, f} ⊆ F whose two elements are disjoint is at least α·C(n, 2); reason: the proof sums over unordered pairs {e, f} ⊆ F, and Lemma 10 counts F_1 × F_2 with F_1, F_2 disjoint, i.e. unordered pairs
--   - encoding: Var X → E X² − (E X)² (varX); reason: the two standard expressions of the variance are equal
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 9 (PDF 10), §3.4, definition of disjoint pairs and Lemma 8

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_8 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (α : ℝ) (hα : 0 < α)
    (hpairs : α * (n.choose 2 : ℝ) ≤ (disjointPairCount (pairSet τA τB) : ℝ)) :
    α ≤ varX (pairSet τA τB) := by sorry

end RendezvousKn.Sym
