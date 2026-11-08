-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_lemma_3_remark
-- name    : QRetrieval.Adaptive.lemma_3_remark
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:55.282277+00:00
-- url     : https://prove2.me/theorems/1b6accf6-c8e6-473b-b249-a428e51b3d68
-- title:
--   Remark after Lemma 3 — every set of at most $n$ left vertices is saturated by a matching
-- statement:
--   Let $G:[k]\times[d]\to[2n]$ be a bipartite graph in which every set $A\subseteq[k]$ with $|A|\le n$ satisfies $|\Gamma_G(A)|\ge|A|$ (the property of Lemma 3). Then for every $A\subseteq[k]$ with $|A|\le n$ there are labels $(e_a\in[d]:a\in A)$ such that
--
--   $$
--   \bigl(G(a,e_a):a\in A\bigr)\ \text{ is a sequence of }|A|\text{ distinct elements of }[2n],
--   $$
--
--   that is, $G$ contains a matching that saturates $A$.
--
--   This is how the expander is used in Lemma 6: the non-zero blocks of a string are matched to distinct slots, and the label $e_a$ of each block is what the quantum probe recovers.
--
--   **Formalization Note** The labels form a function $e:A\to\mathrm{Fin}\,d$ on the elements of $A$, and distinctness is injectivity of $a\mapsto G(a,e_a)$.
--
--   Differences from the source:
--   - generalization: graphs promised by Lemma 3 (degree d = O(max{log(k/n),1}) and the expansion property) → any G : Fin k → Fin d → Fin (2 * n) with the expansion property, any d; reason: the matching uses only the expansion property; graphs from Lemma 3 satisfy the hypothesis
--   - encoding: labels (e_a ∈ [d] : a ∈ A) with (G(a, e_a) : a ∈ A) distinct → e : ↥A → Fin d with fun a => G a (e a) injective; reason: the same family of labels, indexed by the elements of A
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §2.1, Remark after Lemma 3 (unnumbered), p. 5

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_neighbors

namespace QRetrieval.Adaptive

/-- **Remark after Lemma 3 (a matching saturating every set of at most `n` left vertices).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §2.1, Remark after Lemma 3 (unnumbered), p. 5: "In particular, for graphs
promised by the above lemma, by Hall's theorem, for every set `A ⊆ [k]` of size at most `n`, there
is a matching in `G` that saturates `A`. That is, for every such set `A`, we can find labels
`(e_a ∈ [d] : a ∈ A)` such that `(G(a, e_a) : a ∈ A)` is a sequence of `|A|` distinct elements in
`[2n]`."

Let `G : Fin k → Fin d → Fin (2n)` satisfy the conclusion of Lemma 3: `|A| ≤ |Γ_G(A)|` for every
`A ⊆ Fin k` with `|A| ≤ n`. Then for every `A` with `|A| ≤ n` there are labels `e : A → Fin d`
such that `a ↦ G(a, e_a)` is injective on `A`.

**Formalization Note.** "Graphs promised by the above lemma" is the hypothesis `hG` (the
expansion property only; the degree bound plays no role). The labels are indexed by the elements
of `A` (`e : ↥A → Fin d`), as in the paper's `(e_a ∈ [d] : a ∈ A)`; "a sequence of `|A|` distinct
elements" is injectivity of `a ↦ G a (e a)` on `A`. -/
theorem lemma_3_remark {n k d : ℕ} (G : Fin k → Fin d → Fin (2 * n))
    (hG : ∀ A : Finset (Fin k), A.card ≤ n → A.card ≤ (neighbors G A).card)
    (A : Finset (Fin k)) (hA : A.card ≤ n) :
    ∃ e : A → Fin d, Function.Injective fun a : A => G a (e a) := by sorry

end QRetrieval.Adaptive
