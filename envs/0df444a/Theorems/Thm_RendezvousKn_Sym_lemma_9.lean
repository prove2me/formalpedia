-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_9
-- name    : RendezvousKn.Sym.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:08.659343+00:00
-- url     : https://prove2.me/theorems/a48b7763-4c6f-4001-8056-5e13823abd08
-- title:
--   Lemma 9, p. 10 — a bipartite graph with n-vertex sides, (11/12)n ≤ |E| ≤ n and degrees ≤ (2/3)n has two edge sets of size ≥ n/8, every edge of one disjoint from every edge of the other
-- statement:
--   Let $G=(A,B,E)$ be a bipartite graph whose sides $A$ and $B$ have $n$ vertices each, such that
--   $$\tfrac{11}{12}\,n\ \le\ |E|\ \le\ n$$
--   and every vertex of $G$ has degree at most $\tfrac23 n$. Then there are two disjoint subsets of edges $E_1,E_2\subseteq E$, each of size at least $n/8$, such that every edge of $E_1$ is disjoint from every edge of $E_2$ (the two edges share no endpoint).
--
--   Applied to the bipartite graph whose edge set is the pair set $F$, this produces the quadratic number of disjoint pairs that Lemma 8 needs.
--
--   Differences from the source:
--   - generalization: stated under §3's standing assumption n ≥ 2 → no hypothesis on n; reason: for n = 1 the hypotheses are unsatisfiable (|E| ≤ 1 and degrees ≤ 2/3 force E = ∅, against |E| ≥ 11/12) and for n = 0 the empty sets work; the statement specializes to the source's at n ≥ 2
--   - encoding: a bipartite graph with sides A, B of size n; deg(u) the number of edges at u → finite types A, B of cardinality n and an edge set E ⊆ A × B; the degree of a ∈ A is |{e ∈ E : e.1 = a}|, of b ∈ B is |{e ∈ E : e.2 = b}|; reason: a simple bipartite graph is exactly its set of edges between the two sides
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 10 (PDF 11), §3.5, Lemma 9

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_9 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) (hA : Fintype.card A = n) (hB : Fintype.card B = n) (E : Finset (A × B))
    (hElo : (11 / 12 : ℝ) * n ≤ (E.card : ℝ)) (hEhi : E.card ≤ n)
    (hdegA : ∀ a : A, ((E.filter fun e => e.1 = a).card : ℝ) ≤ 2 / 3 * n)
    (hdegB : ∀ b : B, ((E.filter fun e => e.2 = b).card : ℝ) ≤ 2 / 3 * n) :
    ∃ E₁ E₂ : Finset (A × B), E₁ ⊆ E ∧ E₂ ⊆ E ∧ Disjoint E₁ E₂ ∧
      (n : ℝ) / 8 ≤ (E₁.card : ℝ) ∧ (n : ℝ) / 8 ≤ (E₂.card : ℝ) ∧
      ∀ e ∈ E₁, ∀ f ∈ E₂, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by sorry

end RendezvousKn.Sym
