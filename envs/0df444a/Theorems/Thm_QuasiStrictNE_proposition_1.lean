-- Prove2me | Theorems.Thm_QuasiStrictNE_proposition_1
-- name    : QuasiStrictNE.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:38.965542+00:00
-- url     : https://prove2.me/theorems/4f3f7ec0-332b-4b18-8556-8a6a38f243db
-- title:
--   Proposition 1 — $K(C,p)$ is a simplicial complex with $|K(C,p)|=|C|$
-- statement:
--   Let $C$ be a polyhedral complex in $\mathbb R^d$ and, for every $F\in C$, let $p_F\in\mathrm{relint}\,F$. Then the collection
--   $$
--   K(C,p)=\{\mathrm{conv}\{p_{F_0},\dots,p_{F_r}\} : F_0\subsetneq\cdots\subsetneq F_r,\ F_i\in C\}
--   $$
--   is a simplicial complex, and its underlying space equals that of $C$:
--   $$
--   |K(C,p)|=|C|.
--   $$
--   This refines the best-response subdivisions of the strategy simplices to simplicial complexes; the paper cites it from Björner.
--
--   Differences from the source:
--   - reading: the intersection of any two polytopes of C is a face of each of them (Definition 3, clause 2) → the intersection is empty or a face of each (IsPolyhedralComplex); reason: faces are nonempty, so the literal clause would exclude disjoint cells; the paper only treats nonempty intersections (p.10)
--   - encoding: faces: nonempty subsets obtained by turning inequalities into equalities → nonempty exposed faces (IsExposed); reason: the two notions agree for polytopes given by inequalities; no instance changes
--   - encoding: relint F (interior in the affine hull); a fixed point pF per face → intrinsicInterior ℝ F; the selection is a function p on sets with p F ∈ intrinsicInterior ℝ F for F in the complex; reason: Lean convention; same selections
--   - encoding: K(C, p) is a set of simplices conv{pF0, …, pFr} → a Mathlib Geometry.SimplicialComplex whose faces (vertex sets) are exactly the sets {pF0, …, pFr} and whose space is ⋃₀ C; reason: Mathlib records a simplex by its vertex set; same complex
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Proposition 1, p.6

import Mathlib
import Definitions.Def_QuasiStrictNE_IsPolyhedralComplex
import Definitions.Def_QuasiStrictNE_KCp

namespace QuasiStrictNE

/-- **Proposition 1** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Proposition 1, p.6: "The collection K(C, p) is a simplicial complex with
the same underlying space as C: |K(C, p)| = |C|"; the paper cites [Björner 1995, §12.2]).

For every polyhedral complex `C` in `ℝ^d` and every choice `p` of a point `p F ∈ relint F` for each
`F ∈ C`, there is a geometric simplicial complex whose simplices are exactly the convex hulls of
`{p F₀, …, p F_r}` over the chains `F₀ ⊊ ⋯ ⊊ F_r` of `C`, and whose underlying space is the union of
the members of `C`.

**Formalization Note** Simplicial complexes are Mathlib's `Geometry.SimplicialComplex` (faces are
vertex sets; affine independence and proper intersection are part of the structure), `relint` is
`intrinsicInterior ℝ`, and `|C|` is `⋃₀ C`. -/
theorem proposition_1 {d : ℕ} (C : Set (Set (Fin d → ℝ))) (hC : IsPolyhedralComplex C)
    (p : Set (Fin d → ℝ) → (Fin d → ℝ)) (hp : ∀ F ∈ C, p F ∈ intrinsicInterior ℝ F) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin d → ℝ), K.faces = KCp C p ∧ K.space = ⋃₀ C := by sorry

end QuasiStrictNE
