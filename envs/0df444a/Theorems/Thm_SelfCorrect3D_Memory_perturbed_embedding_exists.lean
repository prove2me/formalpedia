-- Prove2me | Theorems.Thm_SelfCorrect3D_Memory_perturbed_embedding_exists
-- name    : SelfCorrect3D.Memory.perturbed_embedding_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:48.444859+00:00
-- url     : https://prove2.me/theorems/08aebc58-1aa0-4f6b-aa39-c5967b0b7071
-- title:
--   Lemma 3.3 — a $(t,1)$-embedding can be perturbed into a $(t',\ell)$-embedding
-- statement:
--   For all degree bounds $z_v,z_e$ there is $t'\in\mathbb N$ such that for every $t\in\mathbb N$ there is $\ell>1$ with the following property. Let $X$ be a finite square complex whose vertex degrees are at most $z_v$ and whose edge degrees are at most $z_e$. If $X$ has a $(t,1)$-embedding in $\mathbb R^3$, then it has a $(t',\ell)$-embedding in $\mathbb R^3$.
--
--   Here a $(t,\ell)$-embedding (Definition 3.1) maps vertices to $\mathbb R^3$ so that every closed unit ball meets the images of at most $t$ squares and every edge has length at most $\ell$. The lemma is the perturbation step that keeps the embedding of every level of the construction local and of bounded density.
--
--   Differences from the source:
--   - reading: "where t, t′ < t and ℓ > 1 are universal O(1) constants independent of i" → ∀ z_v z_e ∃ t′ ∀ t ∃ ℓ > 1; reason: the printed clause is garbled; p. 23 says t′ "can be made small enough" and "ℓ will depend on t and t′", §3.4 takes t′ ≤ 5595 against t = 6.6 × 10^10, and for t > t′ this gives t′ < t; the reading ∀ t ∃ t′ < t is false for small t (a single square has a (1,1)-embedding and no (0,ℓ)-embedding)
--   - generalization: the complexes T_(i) with z_v = 7 and z_e = 4 (p. 22) → every finite square complex with vertex degrees ≤ z_v and edge degrees ≤ z_e, for all z_v, z_e; reason: specializes to the paper's complexes at (z_v, z_e) = (7, 4)
--   - reading: images of 2-cells "obtained via linear interpolation" (p. 21) → the two triangles conv{Iv0, Iv1, Iv2} ∪ conv{Iv0, Iv2, Iv3}; reason: the proof triangulates the squares (p. 23, step 1: "We formally add diagonal lines to the square 2-cells")
--   - encoding: unit ball → closed ball of radius 1; reason: Lean convention for the ball in Definition 3.1
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Lemma 3.3, p. 23, with Definition 3.1, pp. 22–23

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_SquareComplex

namespace SelfCorrect3D.Memory

/-- **Lemma 3.3 (perturbation step).** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Lemma 3.3, p. 23, with
Definition 3.1, pp. 22–23: "If I_(i) is a (t, 1)-embedding of T_(i) in ℝ³, there exists another
embedding map I′_(i) of T_(i) in ℝ³ that is a (t′, ℓ)-embedding, where t, t′ < t and ℓ > 1 are
universal O(1) constants independent of i."

For every bound `(z_v, z_e)` on vertex and edge degrees there is `t′` such that for every `t`
there is `ℓ > 1` with: every finite square complex with vertex degrees `≤ z_v` and edge degrees
`≤ z_e` that has a `(t, 1)`-embedding also has a `(t′, ℓ)`-embedding.

**Formalization Note (reading).** The printed "t, t′ < t" is garbled; it is read as: `t′` depends
only on the degree bounds (p. 23: "The constant t′ can be made small enough"; §3.4 takes
`t′ ≤ 5595` against `t = 6.6 × 10¹⁰`) and `ℓ` on `t` and `t′` (p. 23: "ℓ will depend on t and t′");
for `t > t′` this gives `t′ < t`. The reading "∀ t ∃ t′ < t" is false for small `t` (a single square
has a `(1, 1)`-embedding and no `(0, ℓ)`-embedding). Squares are embedded as two triangles along a
diagonal (`squareImage`); closed unit balls. Generalized from the paper's `(z_v, z_e) = (7, 4)`
(p. 22) and the complexes `T_(i)` to any degree bounds and any finite square complex. -/
theorem perturbed_embedding_exists :
    ∀ zv ze : ℕ, ∃ t' : ℕ, ∀ t : ℕ, ∃ ℓ : ℝ, 1 < ℓ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (X : SquareComplex V),
        (∀ v, X.vertexDegree v ≤ zv) → (∀ e ∈ X.edges, X.edgeDegree e ≤ ze) →
        ∀ I : V → EuclideanSpace ℝ (Fin 3), X.IsEmbedding I t 1 →
          ∃ I' : V → EuclideanSpace ℝ (Fin 3), X.IsEmbedding I' t' ℓ := by sorry

end SelfCorrect3D.Memory
