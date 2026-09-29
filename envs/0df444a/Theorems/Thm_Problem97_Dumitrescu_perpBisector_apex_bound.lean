-- Prove2me | Theorems.Thm_Problem97_Dumitrescu_perpBisector_apex_bound
-- name    : Problem97.Dumitrescu.perpBisector_apex_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:57:27.287815+00:00
-- url     : https://prove2.me/theorems/2f2c4a05-34b4-4ed0-822f-8627a79cd988
-- title:
--   At most two convex vertices lie on a perpendicular bisector
-- statement:
--   Let $A$ be a finite convex-independent set in the Euclidean plane, and let $a,b\in A$ be distinct. At most two points $p\in A$ satisfy $d(p,a)=d(p,b)$. Thus any fixed base pair can support at most two isosceles triangles with apex in $A$, which is the basic per-edge bound in the double count.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_Dumitrescu_perpBisector_apex_bound.lean#L1-L76

/- Generated theorem stub from Erdos9796Proof.P97.Dumitrescu.L1 by Stage 2 proof cut; source SHA-256 170e1886e820b6afa033edfc08e0c4f73057cb7f3c71cc97552cede97ff21fbf -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Hull
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
open Problem97 Problem97.Dumitrescu



/-!
# Dumitrescu L1: perpendicular-bisector apex bound (Problem 97)

`Problem97.Dumitrescu.perpBisector_apex_bound` is Dumitrescu's Lemma 1
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2):

  For any convex-independent finite point set `A ⊆ ℝ²` and any base edge
  `(a, b)` with `a, b ∈ A` and `a ≠ b`, at most `2` points of `A` lie on
  the perpendicular bisector of the segment `ab`.

This is the "perpendicular-bisector apex bound" used in the
isosceles-count double-count argument. It corresponds to the blueprint
obligation `p97-dumitrescu-l1-perp-bisector-apex`.

## Proof strategy

A point `p` lies on the perpendicular bisector of `ab` iff
`dist p a = dist p b` (Mathlib's `AffineSubspace.mem_perpBisector_iff_dist_eq`).

Suppose, for contradiction, that three distinct points `p, q, r ∈ A` all
lie on this perpendicular bisector. Then:

* `q -ᵥ p` and `r -ᵥ p` both lie in the direction of the perpendicular
  bisector, which equals `(ℝ ∙ (b -ᵥ a))ᗮ`
  (Mathlib's `AffineSubspace.direction_perpBisector`).
* In `EuclideanSpace ℝ (Fin 2)`, this orthogonal complement has dimension
  `1` (since `a ≠ b` makes `b -ᵥ a` nonzero, and
  `Submodule.finrank_orthogonal_span_singleton` then gives finrank `1`).
* `q -ᵥ p ≠ 0` (since `p ≠ q`), so `ℝ ∙ (q -ᵥ p)` and `(ℝ ∙ (b -ᵥ a))ᗮ`
  are two `1`-dimensional subspaces of `ℝ²` with the first contained in
  the second, hence equal (`Submodule.eq_of_le_of_finrank_eq`).
* In particular `r -ᵥ p ∈ ℝ ∙ (q -ᵥ p)`, so `r -ᵥ p` is a scalar
  multiple of `q -ᵥ p`. This gives `Collinear ℝ {p, q, r}` directly via
  `collinear_iff_of_mem` (each point is a scalar multiple of `q -ᵥ p`
  added to `p`).

Once `{p, q, r}` is collinear, `Collinear.wbtw_or_wbtw_or_wbtw` says one
of the three lies on the segment between the other two. That point then
lies in the convex hull of the other two, which is a subset of
`convexHull ℝ (A \ {it})`, contradicting `ConvexIndep A`.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

theorem Problem97.Dumitrescu.perpBisector_apex_bound
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {a b : ℝ²} (_ha : a ∈ A) (_hb : b ∈ A) (hab : a ≠ b) :
    (A.filter (fun p => dist p a = dist p b)).card ≤ 2 := by sorry
