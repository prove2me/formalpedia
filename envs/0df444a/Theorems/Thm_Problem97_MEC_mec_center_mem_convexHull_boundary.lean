-- Prove2me | Theorems.Thm_Problem97_MEC_mec_center_mem_convexHull_boundary
-- name    : Problem97.MEC.mec_center_mem_convexHull_boundary
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:01:20.070848+00:00
-- url     : https://prove2.me/theorems/3112fe0b-fc5a-4447-98fd-0788464690a7
-- title:
--   The minimum-enclosing-circle center lies in the hull of its contact points
-- statement:
--   Let $A$ be a nonempty, noncollinear finite planar set. The center of its minimum enclosing circle belongs to the convex hull of the points of $A$ that lie on the circle. This variational support theorem is used to obtain a non-obtuse circumscribed support triangle.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_MEC_mec_center_mem_convexHull_boundary.lean#L1-L142

/- Generated theorem stub from Erdos9796Proof.P97.Moser.TriangleNonObtuse by Stage 2 proof cut; source SHA-256 2a8d00cd1d6b2290156c6085675919cde734d3890ca0877876d719ff756a7348 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
open Problem97 Problem97.MEC



/-!
# Non-obtuse Moser triangle in the circumscribed branch

In the **circumscribed branch** of the Sylvester (1857) dichotomy
(`Problem97.MEC.sylvester_dichotomy`), at least three points of `A` lie on the
MEC boundary.  This file extracts a *non-obtuse* such triple: three distinct
boundary points `a, b, c` of `A` whose triangle has all three vertex angles
at most `π / 2`, equivalently

  `⟪b - a, c - a⟫_ℝ ≥ 0`, `⟪c - b, a - b⟫_ℝ ≥ 0`, `⟪a - c, b - c⟫_ℝ ≥ 0`.

The proof route is Carathéodory in dimension 2.  Let
`B := { p ∈ A | dist p O = r }` be the MEC boundary realisers
(`O = (mec A hA).center`, `r = (mec A hA).radius`).

* **Welzl invariant.**  `O ∈ convexHull ℝ (B : Set ℝ²)`.  Otherwise the
  closed-convex projection of `O` onto `convexHull ℝ B` gives a separating
  direction `v - O` with `⟪p - O, v - O⟫ ≥ ‖v - O‖² > 0` for every `p ∈ B`.
  Translating the centre by a small multiple of `v - O` strictly decreases
  the enclosing radius, contradicting MEC minimality.
* **Carathéodory in dim 2.**  Apply `Caratheodory.minCardFinsetOfMemConvexHull`
  to `O ∈ conv B`: there is an affinely independent `T ⊆ B` with
  `O ∈ convexHull ℝ T`.  Affine independence in `ℝ²` caps `T.card ≤ 3`.
* **Case split on `T.card`.**
  * `card = 1`: `O ∈ {p} ⊆ B` would force `dist p O = 0 = r`, but `r > 0` for
    noncollinear `A`.  Contradiction.
  * `card = 2`: `T = {p, q}`, `O` on segment `[p, q]`.  Boundary equidistance
    + segment membership forces `O = midpoint p q` with `dist p q = 2 r` —
    the diameter configuration.  Pick any third boundary point
    `c ∈ B \ {p, q}` (available by the hypothesis `3 ≤ B.card`).  The right
    angle at `c` (Thales) plus the acute angles at `p, q` give the three
    inner-product inequalities.
  * `card = 3`: `T = {a, b, c}` distinct.  `O ∈ conv {a, b, c}` rewrites as
    a barycentric combination `O = α • a + β • b + γ • c`; the algebraic
    identity `signedArea2 O a b * signedArea2 c a b = γ · signedArea2 c a b²`
    gives the "same-side" condition for each chord, which converts to the
    inner-product nonnegativity via
    `Problem97.signedArea_prod_eq_inner_mul_dist_sq` (forward direction).

## Main results

* `Problem97.MEC.mec_center_mem_convexHull_boundary` — Welzl invariant.
* `Problem97.MEC.exists_nonobtuse_circumscribed_triple` — extraction of the
  non-obtuse boundary triple.
* `Problem97.MEC.nonobtuseCircumscribedMoserTriangle` — packaging into
  the existing `MoserTriangle` structure.
* `Problem97.MEC.nonobtuseCircumscribedMoserTriangle_nonobtuse` — the three
  inner-product nonnegativity inequalities for the packaged triangle.
-/

open scoped EuclideanGeometry InnerProductSpace
open Finset




/- ### Auxiliary: shrink-along-direction identity and small numerical lemmas. -/





/- ### MEC boundary set -/

-- Reuse MEC boundary lemmas from `MEC.Boundary` for a single canonical source
-- of `boundary`, `boundary_nonempty`, `mem_boundary_iff`, and `mec_radius_pos`.

/- ### Sub-lemma X: Welzl invariant -/

theorem Problem97.MEC.mec_center_mem_convexHull_boundary
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    (mec A hA).center ∈
      convexHull ℝ ((boundary A hA : Finset ℝ²) : Set ℝ²) := by sorry
