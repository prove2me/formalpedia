-- Prove2me | Theorems.Thm_QGraphColl_lemma_C_1
-- name    : QGraphColl.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:26.653784+00:00
-- url     : https://prove2.me/theorems/1f3cca54-5bf9-4460-b385-8339964ee51e
-- title:
--   Lemma C.1 — marked counts in a piece: $|M\cap A|\le ap$, $|M\cap B|\le bp$ with $p=\min\{1,\gamma\ell/m\}$
-- statement:
--   Let $G$ be a piece as produced by Lemma C.2: bipartite with sides $A,B$ of sizes $a,b$ consisting of its incident labels, with $m\ge1$ edges, every degree on $A$ in $[d_A/\gamma,d_A]$ and every degree on $B$ in $[d_B/\gamma,d_B]$, for some $\gamma>0$. Then
--
--   1. its degrees on $A$ lie between $m/(\gamma a)$ and $\gamma m/a$, and on $B$ between $m/(\gamma b)$ and $\gamma m/b$;
--   2. if its marked volume is at most $\ell$, then with $p=\min\{1,\gamma\ell/m\}$
--   $$|M\cap A|\le ap,\qquad |M\cap B|\le bp;$$
--   3. these marked count bounds remain valid after edge deletions $G'\subseteq G$, the side labels $A,B$ being fixed (and still sides of $G'$).
--
--   These count bounds are the hypotheses $|M\cap A|\le ap$, $|M\cap B|\le bp$ of Lemmas 4.3 and 4.7.
--
--   Differences from the source:
--   - reading: 'a piece' with sides A, B, sizes a, b, and m edges → IsSides G A B, every vertex of A ∪ B has positive degree, degrees in [d_A/γ, d_A] on A and [d_B/γ, d_B] on B, γ > 0; reason: the proof derives the degree window 'for pieces from Lemma C.2' (p.49), whose pieces have exactly these properties
--   - encoding: p = min{1, γℓ/m} → m ≥ 1; reason: p is undefined at m = 0, and pieces are nonempty (Lemma C.2)
--   - encoding: a bipartite graph with sides A, B → IsSides G A B on a vertex type V that may contain further labels outside A ∪ B; reason: such labels are isolated (every edge joins A to B), and the conclusions concern only edges and the labels incident to them; every bipartite graph has such sides
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma C.1, p.49

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict

namespace QGraphColl

/-- **Lemma C.1** (Marked counts in a piece; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.49). Let a piece have sides `A, B`, sizes
`a, b`, and `m` edges. Its degrees on `A` lie between `m/(γa)` and `γm/a`, and similarly on `B`.
If its marked volume is at most `ℓ`, let `p = min{1, γℓ/m}`. Then `|M ∩ A| ≤ ap` and
`|M ∩ B| ≤ bp`. These marked count bounds remain valid after edge deletions when the side labels
are fixed.

**Formalization Note.**
* A piece is as returned by Lemma C.2 (the proof derives the degree window "for pieces from Lemma
  C.2"): `G` is bipartite with sides `A, B`, `A` and `B` are its incident labels (every vertex of
  `A ∪ B` has positive degree), every degree on side `A` lies in `[d_A/γ, d_A]` and on side `B` in
  `[d_B/γ, d_B]`, and `γ > 0`.
* `m ≥ 1`: `p = min{1, γℓ/m}` is undefined at `m = 0`, and pieces are nonempty (Lemma C.2).
* The last clause: for every edge deletion `G' ≤ G`, `A, B` are still sides of `G'` and the same
  count bounds hold (they concern only the fixed labels and input bits). -/
theorem lemma_C_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : IsSides G A B) (hinc : ∀ v ∈ A ∪ B, 0 < deg G v) (hm : 1 ≤ numEdges G)
    (γ : ℝ) (hγ : 0 < γ) (dA dB : ℝ)
    (hA : ∀ v ∈ A, dA / γ ≤ (deg G v : ℝ) ∧ (deg G v : ℝ) ≤ dA)
    (hB : ∀ v ∈ B, dB / γ ≤ (deg G v : ℝ) ∧ (deg G v : ℝ) ≤ dB) :
    (∀ v ∈ A, (numEdges G : ℝ) / (γ * A.card) ≤ (deg G v : ℝ) ∧
      (deg G v : ℝ) ≤ γ * numEdges G / A.card) ∧
    (∀ v ∈ B, (numEdges G : ℝ) / (γ * B.card) ≤ (deg G v : ℝ) ∧
      (deg G v : ℝ) ≤ γ * numEdges G / B.card) ∧
    (∀ (ℓ : ℝ) (x : V → Bool), (vol G Finset.univ x : ℝ) ≤ ℓ →
      ((marked x ∩ A).card : ℝ) ≤ A.card * min 1 (γ * ℓ / numEdges G) ∧
      ((marked x ∩ B).card : ℝ) ≤ B.card * min 1 (γ * ℓ / numEdges G) ∧
      ∀ G' : SimpleGraph V, G' ≤ G → IsSides G' A B ∧
        ((marked x ∩ A).card : ℝ) ≤ A.card * min 1 (γ * ℓ / numEdges G) ∧
        ((marked x ∩ B).card : ℝ) ≤ B.card * min 1 (γ * ℓ / numEdges G)) := by sorry

end QGraphColl
