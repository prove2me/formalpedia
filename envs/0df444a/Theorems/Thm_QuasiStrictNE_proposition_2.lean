-- Prove2me | Theorems.Thm_QuasiStrictNE_proposition_2
-- name    : QuasiStrictNE.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:09.717218+00:00
-- url     : https://prove2.me/theorems/2421ab56-a6a4-4640-8b21-271a96dfea5a
-- title:
--   Proposition 2 — simplicial maps are well defined and continuous
-- statement:
--   Let $K$ and $L$ be simplicial complexes and let $f$ be a vertex map such that whenever $v_0,\dots,v_r$ span a simplex of $K$, the points $f(v_0),\dots,f(v_r)$ are vertices of a simplex of $L$. Then the map $g:|K|\to|L|$ defined on each simplex by
--   $$
--   g\Bigl(\sum_{i=0}^r t_i v_i\Bigr)=\sum_{i=0}^r t_i f(v_i),\qquad t_i\ge 0,\ \sum_i t_i=1,
--   $$
--   is well defined (it does not depend on the simplex used) and continuous: it is continuous on every closed simplex of $K$, which is continuity for the coherent topology of $|K|$, and for finite $K$ it is continuous on $|K|\subseteq\mathbb R^d$.
--
--   Differences from the source:
--   - reading: simplicial complexes K, L (Definition 2) with |K| carrying its topology → g is continuous on every closed simplex of K (the coherent topology of |K|, any K) and, when K.faces is finite, on K.space ⊆ ℝ^d (subspace topology); reason: Definition 2 does not require K finite and the paper names no topology on |K|; the paper follows Munkres, whose topology is the coherent one; for finite complexes, all the paper uses (Definition 3, Proposition 1), it is the subspace topology, and for infinite K continuity in the subspace topology fails
--   - encoding: a vertex map f : K(0) → L(0) whose images of the vertices of a simplex are vertices of a simplex of L → f : ℝ^d → ℝ^e with σ.image f ∈ L.faces for every face σ of K; reason: only values at vertices matter; L is closed under faces, so 'vertices of a simplex' is 'a simplex'
--   - encoding: well-defined map g on |K| → ∃ g satisfying the barycentric formula on every simplex and mapping K.space into L.space; reason: well-definedness is the existence of one map agreeing with the formula on every simplex
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Proposition 2 and Definition 5, p.7

import Mathlib

namespace QuasiStrictNE

open Classical in
/-- **Proposition 2** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Proposition 2, p.7: "The simplicial map g : |K| → |L| induced by a
vertex map satisfying the above condition is well-defined and continuous"; Definition 5, p.7).

Let `K` and `L` be simplicial complexes in `ℝ^d` and `ℝ^e`, and let `f` be a vertex map
such that the images of the vertices of every simplex of `K` are the vertices of a simplex of `L`.
Then there is a map `g` with `g(∑ tᵥ v) = ∑ tᵥ f(v)` for every simplex `σ` of `K` and all barycentric
weights `t ≥ 0`, `∑ tᵥ = 1` on its vertices (well-definedness), which maps `|K|` into `|L|`, is
continuous on every closed simplex of `K`, and, when `K` is finite, is continuous on `|K|` as a subset
of `ℝ^d`.

**Formalization Note** Simplicial complexes are Mathlib's `Geometry.SimplicialComplex`. The vertex
map is a function on `ℝ^d`, of which only the values at vertices of `K` matter; "f(v0), …, f(vr) are
vertices of a simplex of L" is "the image of the vertex set of every simplex of `K` is a simplex of
`L`" (simplicial complexes are closed under taking faces). Definition 2 does not require `K` to be finite and
the paper names no topology on `|K|`. Continuity on every closed simplex is continuity for the coherent
(weak) topology of `|K|` (Munkres), for every `K`. For finite `K`, the case of all the paper's complexes,
that topology is the subspace topology of `ℝ^d`, which is the last clause; for infinite `K` continuity in
the subspace topology can fail (vertices `1/k` and `0` in `ℝ` with alternating images). -/
theorem proposition_2 {d e : ℕ} (K : Geometry.SimplicialComplex ℝ (Fin d → ℝ))
    (L : Geometry.SimplicialComplex ℝ (Fin e → ℝ))
    (f : (Fin d → ℝ) → (Fin e → ℝ)) (hf : ∀ σ ∈ K.faces, σ.image f ∈ L.faces) :
    ∃ g : (Fin d → ℝ) → (Fin e → ℝ),
      (∀ σ ∈ K.faces, ∀ t : (Fin d → ℝ) → ℝ, (∀ v ∈ σ, 0 ≤ t v) → ∑ v ∈ σ, t v = 1 →
        g (∑ v ∈ σ, t v • v) = ∑ v ∈ σ, t v • f v) ∧
      Set.MapsTo g K.space L.space ∧
      (∀ σ ∈ K.faces, ContinuousOn g (convexHull ℝ (σ : Set (Fin d → ℝ)))) ∧
      (K.faces.Finite → ContinuousOn g K.space) := by sorry

end QuasiStrictNE
