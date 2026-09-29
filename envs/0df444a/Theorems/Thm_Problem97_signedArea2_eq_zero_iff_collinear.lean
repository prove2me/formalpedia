-- Prove2me | Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear
-- name    : Problem97.signedArea2_eq_zero_iff_collinear
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:14:03.37171+00:00
-- url     : https://prove2.me/theorems/0a228857-44df-489c-a51e-7d4f87638131
-- title:
--   Vanishing Signed Area Characterizes Collinearity
-- statement:
--   For three points in ℝ², their signed area is zero if and only if the three-point set is collinear over ℝ.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_signedArea2_eq_zero_iff_collinear.lean#L1-L168

/- Generated theorem stub from Erdos9796Proof.P97.OangleBridge by Stage 2 proof cut; source SHA-256 f9fbffddedb8e5ece4b3223e436c1d63e2482969b22da45c8d09d8cf9cefcef1 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Simplex
open Problem97



/-!
# Oangle bridge: lift `dist` / `signedArea2` predicates to Mathlib `oangle` / `Cospherical`

This module supplies a small set of bridge lemmas that lift the project's
in-tree vocabulary on the MEC + Moser-triangle infrastructure to Mathlib's
oriented-angle (`EuclideanGeometry.oangle`), cospherical-set
(`EuclideanGeometry.Cospherical`), and equilateral-triangle
(`Affine.Simplex.Equilateral`) vocabulary.

The intended consumers are Phase 1 sublemma 5 ("short-cap Apollonius",
`U1ShortCapApollonius` in `U1TwoShortCapReduction`) and the related U2/U3
geometric content (`U2EquilateralMECFromM44`, `U3ShortCapSaturation`).

Scope of this pass (no proofs in U1/U2/U3 are modified by this file):

* `Problem97.MEC.moserTriangle_v{1,2,3}_mem_mecSphere` — concrete sphere
  membership of the three vertices of a `MoserTriangle`.
* `Problem97.MEC.moserTriangle_cospherical` — the abstract `Cospherical`
  predicate on the vertex-triple.
* `Problem97.MEC.moserTriangle_distinct_of_circumscribed`,
  `Problem97.MEC.moserTriangle_affineIndependent_of_circumscribed` —
  pairwise distinctness + affine independence in the circumscribed branch
  of the Sylvester dichotomy, needed for the oangle/Cospherical converse
  lemmas.
* `Problem97.two_zsmul_oangle_eq_of_mecSphere` — wraps mathlib's
  `Sphere.two_zsmul_oangle_eq` for points on the MEC sphere
  (inscribed-angle theorem in Mathlib's `2 • oangle = 2 • oangle` form).
* `Problem97.cospherical_of_two_zsmul_oangle_eq_of_not_collinear_named` —
  re-export of mathlib's Apollonius converse, named in our namespace so
  downstream callers don't have to chase the open-namespace boilerplate.

No proofs in this file rely on `sorry`, opaque `axiom`s, or vacuous
`True`-placeholders. The harder bridges (the explicit equilateral-side
formula `d = R · √3`, the full chord-side characterization of the 60°
Apollonius arc, the `Real.Angle.pi_div_three` arithmetic at an
equilateral inscribed apex, and the converse direction
`Collinear ↔ signedArea2 = 0`) are deliberately *not* included in this
pass — they remain open sub-obligations flagged in
`docs/97-uniform-theorem-closure-plan.md` Phase 1 sublemma 5 and
`docs/97-uniform-theorem-candidate.md`. -/

open scoped EuclideanGeometry





/- ### MEC + Moser-triangle vertices as `Cospherical` data -/









/- ### Distinctness extractors in the circumscribed branch

For all consumers below the diameter branch is `v3 = v1`; pairwise
distinctness only holds in the circumscribed branch. The
`NonObtuseCircumscribedMoserTriangle` wrapper produced by
`MoserTriangleNonObtuse` always sits in the circumscribed branch (built
from `exists_nonobtuse_circumscribed_triple`), but the `case_split`
witness is hidden inside the underlying `MoserTriangle`. The lemmas below
unpack pairwise distinctness from the `case_split` directly. -/







/- ### Inscribed-angle / Apollonius-converse bridges (in `Problem97` namespace)

These are direct wrappers of mathlib's `Sphere.two_zsmul_oangle_eq` and
`cospherical_of_two_zsmul_oangle_eq_of_not_collinear`, named so that
downstream callers can invoke them without re-opening
`EuclideanGeometry`. -/





/- ### Operational Apollonius-arc predicate

The placeholder `Problem97.Abstract60ApolloniusArc` in
`U3ShortCapSaturation` currently unfolds to `True`. The intended
operational form combines an inscribed-angle equality (in Mathlib's
`2 • oangle` form, which is the chart-free statement of "P sees `vj, vk`
at the same angle as `vi` does") with a chord-side condition pinning
`P` to the arc opposite `vi`.

`OpApolloniusArc vi vj vk P` is that operational form, expressed using:

* Mathlib's `EuclideanGeometry.oangle` (modular by `π`, so `2 • oangle`
  identifies the two arcs of a circle).
* The in-tree `Problem97.OnArcOpposite vi vj vk P` (signed-area chord
  side), which is the strict arc-side pin.

This file does not (yet) prove that `OpApolloniusArc` agrees with the
classical 60° arc through `vj, vk` opposite `vi` in the equilateral
inscribed setting. That equivalence is the load-bearing content of
Phase 1 sublemma 5; see
`docs/97-uniform-theorem-closure-plan.md` lines 213–217 and the
`Abstract60ApolloniusArc` `{{NEEDS_RESEARCH}}` marker at
`U3ShortCapSaturation.lean:114`. -/







/- ### Equilateral-inscribed bridge lemmas

These close the four deferred bridge lemmas flagged for Phase 1 of the
uniform-theorem closure plan (`docs/97-uniform-theorem-closure-plan.md`,
sublemma 5). They are stated in the general inner-product / sphere
setting so they can specialise to the MEC sphere `mecSphere A hA` (the
caller substitutes `s := mecSphere A hA`). Together with the existing
`cospherical_of_opApolloniusArc` forward direction, they constitute the
full characterisation of the 60° Apollonius arc:

* lemma 1 — equilateral inscribed side `= R · √3`;
* lemma 2 — equilateral inscribed apex sees the opposite chord at angle
  `π/3` (or, oriented, `(∡ p₁ p₂ p₃).toReal = ±π/3`);
* lemma 3 — cospherical implies the chart-free `2 • oangle` equality
  consumed by `OpApolloniusArc` (the reverse direction of the
  inscribed-angle bridge);
* lemma 4 — `signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ {v₁, v₂, v₃}`
  (one direction is `MoserNonDeg.collinear_of_signedArea2_eq_zero`;
  this file supplies the converse). -/







/- The unsigned theorem above leaves the orientation branch to each caller.
   This small adapter discharges the negative branch from a positive signed
   angle hypothesis, which is the form supplied by the convex cyclic-order
   API. -/

theorem Problem97.signedArea2_eq_zero_iff_collinear (v₁ v₂ v₃ : ℝ²) :
    signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ ({v₁, v₂, v₃} : Set ℝ²) := by sorry
